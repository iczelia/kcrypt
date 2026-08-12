/*  KCrypt - 4th iteration of a cryptographic algorithm.  Written on
    Monday, 3rd of August 2026 by Kamila Szewczyk.  Public domain.  */

#ifdef HAVE_CONFIG_H
  #include "config.h"
#endif
#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <errno.h>
#include <stdarg.h>
#include <ctype.h>
#include <stdlib.h>
#include "yarg.h"

/* -------------------------------------------------------------------------
     Constant-time Galois field arithmetic.
   ------------------------------------------------------------------------- */
typedef uint8_t gf;
enum {
  KC_BLOCK_SIZE = 64, KC_HALF_SIZE = 32, KC_NONCE_SIZE = 16, KC_ROUNDS = 16
};

/*  Optimisation barrier.   */
#if !defined(HAVE_ASM_BARRIER) && (defined(__GNUC__) || defined(__clang__))
  #define HAVE_ASM_BARRIER 1
#endif
#ifdef HAVE_ASM_BARRIER
static gf gf_opaque(gf x) {
  __asm__ volatile ("" : "+r" (x));  return x;
}
#else
static gf gf_opaque(gf x) {
  volatile gf v = x;  return v;
}
#endif

static void wipe(void * buf, size_t n) {
  volatile gf * p = buf;
  while (n--) *p++ = 0;
  #ifdef HAVE_ASM_BARRIER
    __asm__ volatile ("" : : : "memory");
  #endif
}

/*  All ones when the arguments are equal, all zeroes otherwise.  */
static gf gf_eq(gf a, gf b) {
  return gf_opaque((uint32_t) (a ^ b) - 1 >> 8);
}
static gf gf_mul2(gf x) {
  gf c = gf_opaque(-(gf) (x >> 7));
  return x << 1 ^ c & 0x1d;
}
static gf gf_mul(gf a, gf b) {
  gf r = 0;
  for (int i = 0; i < 8; i++) {
    r ^= a & gf_opaque(-(gf) (b & 1));
    b >>= 1;  a = gf_mul2(a);
  }
  return r;
}

/*  The multiplicative inverse is x^254, reached by an addition chain.  Zero
    has no inverse and is mapped to itself.  */
static gf gf_inv(gf x) {
  gf x2 = gf_mul(x, x), x3 = gf_mul(x2, x);
  gf x6 = gf_mul(x3, x3), x12 = gf_mul(x6, x6);
  gf y = gf_mul(x12, x3);                      /* x^15  */
  for (int i = 0; i < 4; i++) y = gf_mul(y, y);   /* x^240 */
  return gf_mul(gf_mul(y, x12), x2);
}

/*  Remainder by bitwise long division.  */
static gf gf_mod(gf x, gf m) {
  uint32_t r = 0;
  for (int i = 7; i >= 0; i--) {
    r += r + (x >> i & 1);
    uint32_t t = r - m;
    r = t + (m & gf_opaque(-(gf) (t >> 31)));
  }
  return r;
}

/* -------------------------------------------------------------------------
     Feistel network.
   ------------------------------------------------------------------------- */
typedef struct { gf k1[32];  gf k2[64]; } block_key_t;
typedef struct {
  gf k2[64];  gf round[16][32];  gf permutation[16][32];
} expanded_key_t;

/*  A Fisher-Yates shuffle whose exchange is applied as a masked swap against
    every position, so the addresses touched do not reveal the key.  */
static void fisher32(const gf k[64], gf x[32], int rd) {
  for (int i = 0; i < 32; i++) x[i] = i;
  for (int i = 31; i > 0; i--) {
    gf j = gf_mod(k[i + rd * 21 & 63], i + 1);
    for (int q = 0; q < 32; q++) {
      gf t = (x[i] ^ x[q]) & gf_eq(q, j);
      x[i] ^= t;  x[q] ^= t;
    }
  }
}

/*  out[i] = in[p[i]], read as a masked scan over the whole input.  */
static void permute32(gf out[32], const gf in[32], const gf p[32]) {
  for (int i = 0; i < 32; i++) {
    gf x = 0;
    for (int q = 0; q < 32; q++) x |= in[q] & gf_eq(q, p[i]);
    out[i] = x;
  }
}

static void diffuse32(gf a[32]) {
  static const unsigned int off[] = { 1, 3, 7, 13 };
  gf b[32];
  for (size_t q = 0; q < sizeof off / sizeof off[0]; q++) {
    for (int i = 0; i < 32; i++)
      b[i] = a[i] ^ gf_mul2(a[i + off[q] & 31]);
    memcpy(a, b, sizeof b);
  }
  wipe(b, sizeof b);
}

/*  The round permutations depend only on the key, so they are derived once
    here rather than being rebuilt for every block that gets encrypted.  */
static void keysched(const block_key_t * k, expanded_key_t * e) {
  gf s[32], n[32], u[32];
  memcpy(s, k->k1, sizeof s);
  memcpy(e->k2, k->k2, sizeof e->k2);
  for (int rd = 0; rd < KC_ROUNDS; rd++) {
    fisher32(e->k2, e->permutation[rd], rd);
    permute32(u, s, e->permutation[rd]);
    for (int i = 0; i < 32; i++) {
      gf m = u[i] ^ gf_mul2(u[i + 1 & 31])
                  ^ e->k2[i + rd * 17 & 63] ^ (rd + 1) * 0x9d + i;
      n[i] = gf_inv(m) + e->k2[i + 32 + rd * 29 & 63];
    }
    diffuse32(n);
    memcpy(e->round[rd], n, sizeof n);
    memcpy(s, n, sizeof s);
  }
  wipe(s, sizeof s);  wipe(n, sizeof n);  wipe(u, sizeof u);
}

static void feistelF(gf b[32], const gf rk[32], const gf k2[64],
                     const gf p[32], int rd) {
  gf u[32];
  permute32(u, b, p);
  for (int i = 0; i < 32; i++) {
    gf m = u[i] ^ gf_mul2(u[i + 1 & 31]) ^ k2[i + 32 + rd * 11 & 63];
    b[i] = rk[i] + gf_inv(m);
  }
  diffuse32(b);
  wipe(u, sizeof u);
}

static void feistel0(gf L[32], gf R[32], const expanded_key_t * e) {
  gf t[32];
  for (int rd = 0; rd < KC_ROUNDS; rd++) {
    memcpy(t, R, sizeof t);
    feistelF(R, e->round[rd], e->k2, e->permutation[rd], rd);
    for (int i = 0; i < 32; i++) R[i] ^= L[i];
    memcpy(L, t, sizeof t);
  }
  wipe(t, sizeof t);
}

static void encode_block(const gf in[64], gf blk[64],
                         const expanded_key_t * e) {
  memcpy(blk, in, 64);
  feistel0(blk, blk + 32, e);
}

/* -------------------------------------------------------------------------
     Secure randomness source.  Supports Windows, DOS and Unix systems.
   ------------------------------------------------------------------------- */
static void eprintf(const char * fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  exit(1);
}

#ifdef _WIN32
#include <windows.h>
#include <fcntl.h>
#include <io.h>
static void secrandom(void * buf, size_t len) {
  HCRYPTPROV hp;
  if (!CryptAcquireContext(&hp, NULL, NULL, PROV_RSA_FULL,
                           CRYPT_VERIFYCONTEXT))
    eprintf("Could not initialise the system random source.\n");
  if (!CryptGenRandom(hp, (DWORD) len, buf)) {
    CryptReleaseContext(hp, 0);
    eprintf("Could not read from the system random source.\n");
  }
  CryptReleaseContext(hp, 0);
}
#elif __unix__
#include <fcntl.h>
#include <unistd.h>
static void secrandom(void * buf, size_t len) {
  int fd = open("/dev/urandom", O_RDONLY);
  if (fd < 0)
    eprintf("Could not open `/dev/urandom': %s\n", strerror(errno));
  gf * p = buf;
  while (len > 0) {
    ssize_t n = read(fd, p, len);
    if (n < 0 && errno == EINTR) continue;
    if (n <= 0) {
      int e = errno;  close(fd);
      if (n == 0)
        eprintf("Could not read from `/dev/urandom': unexpected EOF.\n");
      eprintf("Could not read from `/dev/urandom': %s\n", strerror(e));
    }
    p += (size_t) n;  len -= (size_t) n;
  }
  if (close(fd) < 0)
    eprintf("Could not close `/dev/urandom': %s\n", strerror(errno));
}
#elif __MSDOS__
static void secrandom(void * buf, size_t len) {  /* Doug Kaufman's NOISE.SYS */
  FILE * f = fopen("/dev/urandom$", "rb");
  if (!f)
    eprintf("Could not open `/dev/urandom$': %s\n", strerror(errno));
  if (fread(buf, 1, len, f) < len)
    eprintf("Could not read from `/dev/urandom$': %s\n", strerror(errno));
  fclose(f);
}
#endif

/* -------------------------------------------------------------------------
     Stream ciphers.
   ------------------------------------------------------------------------- */
enum { CIPHER_STREAM_FILE, CIPHER_STREAM_BLOCK, CIPHER_STREAM_FUNCTION };

typedef struct {
  int type;
  uint64_t max;
  union {
    FILE * file;
    struct {
      size_t (* read)(void * ptr, size_t size, size_t nmemb, void * stream);
      size_t (* write)(const void * ptr, size_t size, size_t nmemb,
                       void * stream);
      uint64_t (* tell)(void * stream);
      void * stream;
    } stream;
    struct {
      uint8_t * buffer;
      size_t size, consumed;
    };
  };
} cipher_aux_t;

static void write64_le_buf(uint64_t v, gf b[8]) {
  for (int i = 0; i < 8; i++) b[i] = v >> i * 8;
}

static size_t cipher_aux_fread(void * ptr, size_t size, size_t nmemb,
                               cipher_aux_t * s) {
  if (s->type == CIPHER_STREAM_FILE) {
    size_t n = fread(ptr, size, nmemb, s->file);
    if (n < nmemb && ferror(s->file))
      eprintf("Could not read from the input file: %s\n", strerror(errno));
    return n;
  } else if (s->type == CIPHER_STREAM_FUNCTION)
    return s->stream.read(ptr, size, nmemb, s->stream.stream);
  if (s->consumed + size * nmemb > s->size)
    eprintf("Internal error.\n");
  memcpy(ptr, s->buffer + s->consumed, size * nmemb);
  s->consumed += size * nmemb;
  return nmemb;
}

static size_t cipher_aux_fwrite(const void * ptr, size_t size, size_t nmemb,
                                cipher_aux_t * s) {
  if (!nmemb || !size) return 0;
  if (s->type == CIPHER_STREAM_FILE) {
    if (fwrite(ptr, size, nmemb, s->file) != nmemb)
      eprintf("Could not write to the output file: %s\n", strerror(errno));
    return nmemb;
  } else if (s->type == CIPHER_STREAM_FUNCTION)
    return s->stream.write(ptr, size, nmemb, s->stream.stream);
  if (s->consumed + size * nmemb > s->size)
    eprintf("Internal error.\n");
  memcpy(s->buffer + s->consumed, ptr, size * nmemb);
  s->consumed += size * nmemb;
  return nmemb;
}

static uint64_t cipher_aux_ftell(cipher_aux_t * s) {
  if (s->type == CIPHER_STREAM_FILE) {
    long pos = ftell(s->file);
    return pos < 0 ? 0 : (uint64_t) pos;
  } else if (s->type == CIPHER_STREAM_FUNCTION)
    return s->stream.tell(s->stream.stream);
  return s->consumed;
}

typedef void (* fprogress_cb)(uint64_t processed, uint64_t total);
typedef struct {
  fprogress_cb pcb;
  expanded_key_t key;
  cipher_aux_t input, output;
} mode_params_t;

typedef void (* stream_enc)(mode_params_t * p);
typedef void (* stream_dec)(mode_params_t * p);

static void cipher_check_header(mode_params_t * p, gf nonce[KC_NONCE_SIZE]) {
  if (cipher_aux_fread(nonce, 1, KC_NONCE_SIZE, &p->input) != KC_NONCE_SIZE)
    eprintf("Truncated input.\n");
}

static void cipher_put_header(const char * hdr, mode_params_t * p,
                              gf nonce[KC_NONCE_SIZE]) {
  size_t len = strlen(hdr);
  gf out[6 + KC_NONCE_SIZE];
  if (len != 6)
    eprintf("Internal error: invalid ciphertext header.\n");
  memcpy(out, hdr, len);
  secrandom(nonce, KC_NONCE_SIZE);
  memcpy(out + len, nonce, KC_NONCE_SIZE);
  cipher_aux_fwrite(out, 1, sizeof out, &p->output);
}

/* -------------------------------------------------------------------------
     Standard length-preserving CTR and OFB modes.
   ------------------------------------------------------------------------- */
static void crypt_ctr(mode_params_t * p, int encode) {
  gf nonce[KC_NONCE_SIZE], in[KC_BLOCK_SIZE], out[KC_BLOCK_SIZE];
  gf ctr[KC_BLOCK_SIZE] = { 0 }, ks[KC_BLOCK_SIZE];
  uint64_t counter = 0;  size_t n;

  if (encode) cipher_put_header("KC4CTR", p, nonce);
  else cipher_check_header(p, nonce);
  memcpy(ctr, nonce, sizeof nonce);
  ctr[KC_BLOCK_SIZE - 1] = 1;  /* Mode-domain separator. */

  while ((n = cipher_aux_fread(in, 1, sizeof in, &p->input)) > 0) {
    write64_le_buf(counter, ctr + KC_NONCE_SIZE);
    encode_block(ctr, ks, &p->key);
    for (size_t i = 0; i < n; i++) out[i] = in[i] ^ ks[i];
    cipher_aux_fwrite(out, 1, n, &p->output);
    if (p->pcb)
      p->pcb(cipher_aux_ftell(&p->input), p->input.max);
    if (counter == UINT64_MAX)
      eprintf("Input is too large for CTR mode.\n");
    counter++;
  }
}

static void encode_ctr(mode_params_t * p) { crypt_ctr(p, 1); }
static void decode_ctr(mode_params_t * p) { crypt_ctr(p, 0); }

static void crypt_ofb(mode_params_t * p, int encode) {
  gf nonce[KC_NONCE_SIZE], in[KC_BLOCK_SIZE], out[KC_BLOCK_SIZE];
  gf s[KC_BLOCK_SIZE] = { 0 }, next[KC_BLOCK_SIZE];
  size_t n;

  if (encode) cipher_put_header("KC4OFB", p, nonce);
  else cipher_check_header(p, nonce);
  memcpy(s, nonce, sizeof nonce);
  s[KC_BLOCK_SIZE - 1] = 2;  /* Mode-domain separator. */

  while ((n = cipher_aux_fread(in, 1, sizeof in, &p->input)) > 0) {
    encode_block(s, next, &p->key);
    memcpy(s, next, sizeof s);
    for (size_t i = 0; i < n; i++) out[i] = in[i] ^ s[i];
    cipher_aux_fwrite(out, 1, n, &p->output);
    if (p->pcb)
      p->pcb(cipher_aux_ftell(&p->input), p->input.max);
  }
}

static void encode_ofb(mode_params_t * p) { crypt_ofb(p, 1); }
static void decode_ofb(mode_params_t * p) { crypt_ofb(p, 0); }

/* -------------------------------------------------------------------------
     Command-line stub.
   ------------------------------------------------------------------------- */
enum { MODE_ENCODE, MODE_DECODE, MODE_KEYGEN, MODE_RANDOM };

static uint64_t file_size(FILE * f) {
  long o = ftell(f);
  if (o < 0 || fseek(f, 0, SEEK_END))
    { clearerr(f);  return 0; }
  long n = ftell(f);
  if (fseek(f, o, SEEK_SET) || n < 0)
    { clearerr(f);  return 0; }
  return n;
}

static void detect_mode_of_operation(FILE * f, stream_enc * e,
                                     stream_dec * d) {
  char hdr[6];
  if (fread(hdr, 1, 6, f) != 6)
    eprintf("Truncated input.\n");
  if (!memcmp(hdr, "KC4CTR", 6))      *e = encode_ctr, *d = decode_ctr;
  else if (!memcmp(hdr, "KC4OFB", 6)) *e = encode_ofb, *d = decode_ofb;
  else eprintf("Input corrupted: unknown mode of operation.\n");
}

static void help(void) {
  fprintf(stdout,
    "kcrypt (Mon, 3 Aug 2026) - 4th iteration of the KCrypt algorithm.\n"
    "Usage: kcrypt [-e/d/g/r] [-v/p/h/f/c] [-m mode] [-k key] files...\n"
    "Operations:\n"
    "  -e, --encode        Encode the input file.\n"
    "  -d, --decode        Decode the input file.\n"
    "  -g, --keygen        Generate a new key file.\n"
    "  -r, --random        Generate random data using the key.\n"
    "General options:\n"
    "  -v, --version       Print the version information.\n"
    "  -p, --progress      Show progress information.\n"
    "  -h, --help          Print this help message.\n"
    "  -f, --force         Overwrite existing files.\n"
    "  -c, --stdout        Write output to the standard output.\n"
    "Additional options:\n"
    "  -m, --mode=mode     Set the mode of operation (OFB/CTR).\n"
    "  -k, --key=key       Specify the key file.\n"
    "Written by Kamila Szewczyk (k@iczelia.net).\n"
    "Released to the public domain.\n"
  );
}

static void version(void) {
  fprintf(stdout,
    "kcrypt (Mon, 3 Aug 2026) - 4th iteration of the KCrypt algorithm.\n"
    "Written by Kamila Szewczyk. Released to the public domain.\n"
  );
}

static void progress_callback(uint64_t done, uint64_t total) {
  if (done % 8192 == 0) {
    done /= 1024;  total /= 1024;
    if (!total)
      fprintf(stderr, "\rProcessed: %" PRIu64 "kB.", done);
    else
      fprintf(stderr, "\rProcessed: %" PRIu64 "/%" PRIu64 "kB.", done, total);
  }
}

static size_t zerodev_read(void * ptr, size_t size, size_t nmemb,
                           void * stream) {
  memset(ptr, 0, size * nmemb);
  *(uint64_t *) stream += size * nmemb;
  return nmemb;
}
static size_t zerodev_write(const void * ptr, size_t size, size_t nmemb,
                            void * stream) {
  (void) ptr;  (void) size;  (void) stream;  return nmemb;
}
static uint64_t zerodev_tell(void * stream) {
  return *(uint64_t *) stream;
}

int main(int argc, char * argv[]) {
  yarg_options opt[] = {
    /*  Actions.  */
    { 'e', no_argument,       "encode" },
    { 'd', no_argument,       "decode" },
    { 'g', no_argument,       "genkey" },
    { 'r', no_argument,       "random" },
    /*  General.  */
    { 'v', no_argument,       "version" },
    { 'p', no_argument,       "progress" },
    { 'h', no_argument,       "help" },
    { 'c', no_argument,       "stdout" },
    { 'f', no_argument,       "force" },
    { 'm', required_argument, "mode" },
    { 'k', required_argument, "key" },
    {   0, no_argument,       NULL }
  };
  yarg_settings settings = { .dash_dash = 1, .style = YARG_STYLE_UNIX };
  yarg_result * res = yarg_parse(argc, argv, opt, settings);
  if (!res) eprintf("Out of memory.\n");
  if (res->error)
    eprintf("%s\nTry `kcrypt --help' for more information.\n", res->error);
  int mode = -1, force = 0, progress = 0, to_stdout = 0;
  stream_enc enc = NULL;  stream_dec dec = NULL;
  const char * key_path = NULL;
  for (int i = 0; i < res->argc; i++) {
    switch (res->args[i].opt) {
      case 'e': mode = MODE_ENCODE;  break;
      case 'd': mode = MODE_DECODE;  break;
      case 'g': mode = MODE_KEYGEN;  break;
      case 'r': mode = MODE_RANDOM;  break;
      case 'f': force = 1;  break;
      case 'h': help();  return 0;
      case 'v': version();  return 0;
      case 'p': progress = 1;  break;
      case 'c': to_stdout = 1;  break;
      case 'k': key_path = res->args[i].arg;  break;
      case 'm':
        for (char * p = res->args[i].arg; *p; p++)
          *p = tolower((unsigned char) *p);
        if (!strcmp(res->args[i].arg, "ofb"))
          enc = encode_ofb, dec = decode_ofb;
        else if (!strcmp(res->args[i].arg, "ctr"))
          enc = encode_ctr, dec = decode_ctr;
        else
          eprintf("Unknown mode of operation `%s'.\n", res->args[i].arg);
        break;
    }
  }
  if (mode == -1)
    eprintf("No action specified.\n"
            "Try `kcrypt --help' for more information.\n");
  #if defined(__MSVCRT__)
    setmode(STDIN_FILENO, O_BINARY);
    setmode(STDOUT_FILENO, O_BINARY);
  #endif
  char * f1 = NULL, * f2 = NULL;
  for (int i = 0; i < res->pos_argc; i++) {
    if (f1 && f2) eprintf("Too many positional arguments.\n");
    if (!f1) f1 = res->pos_args[i];  else f2 = res->pos_args[i];
  }
  char * input = NULL, * output = NULL;
  if (f1 || f2) {
    if (mode == MODE_ENCODE) {
      if (!f2) {
        input = f1;
        if (!to_stdout) {
          output = malloc(strlen(f1) + 5);
          strcpy(output, f1);  strcat(output, ".kc4");
        }
      } else input = f1, output = f2;
    } else if (mode == MODE_DECODE) {
      if (!f2) {
        input = f1;
        if (!to_stdout) {
          output = malloc(strlen(f1) + 1);
          strcpy(output, f1);
          if (strlen(f1) > 4 && !strcmp(f1 + strlen(f1) - 4, ".kc4"))
            output[strlen(f1) - 4] = 0;
          else
            eprintf("File `%s' has an unrecognised extension.\n", f1);
        }
      } else input = f1, output = f2;
    } else if (mode == MODE_RANDOM) {
      output = f1;
      if (f2) eprintf("Too many positional arguments.\n");
    } else if (mode == MODE_KEYGEN) {
      if (f1 || f2) eprintf("Too many positional arguments.\n");
    }
  }
  FILE * fin = stdin, * fout = stdout, * fkey = NULL;
  if (input) {
    fin = fopen(input, "rb");
    if (!fin)
      eprintf("Could not open `%s': %s\n", input, strerror(errno));
  }
  if (key_path) {
    #if defined(__unix__)
    if (mode == MODE_KEYGEN) {
      int fd = open(key_path, O_WRONLY | O_CREAT | O_TRUNC, 0600);
      if (fd >= 0) fkey = fdopen(fd, "wb");
      if (fd >= 0 && !fkey) close(fd);
    } else
      fkey = fopen(key_path, "rb");
    #else
    fkey = fopen(key_path, mode == MODE_KEYGEN ? "wb" : "rb");
    #endif
    if (!fkey)
      eprintf("Could not open `%s': %s\n", key_path, strerror(errno));
  }
  if (output && !force && !access(output, F_OK))
    eprintf("File `%s' already exists. Use `-f' to overwrite.\n", output);
  if (output) {
    fout = fopen(output, "wb");
    if (!fout)
      eprintf("Could not open `%s': %s\n", output, strerror(errno));
  }
  switch (mode) {
    case MODE_KEYGEN: {
      if (!fkey) eprintf("No key file specified.\n");
      block_key_t k;  secrandom(&k, sizeof k);
      int ok = fwrite(&k, sizeof k, 1, fkey) == 1;
      wipe(&k, sizeof k);
      if (!ok)
        eprintf("Could not write to key file: %s\n", strerror(errno));
      break;
    }
    case MODE_RANDOM: {
      if (!fkey) eprintf("No key file specified.\n");
      if (!enc || !dec) eprintf("No mode of operation specified.\n");
      block_key_t raw;  expanded_key_t key;
      if (fread(&raw, sizeof raw, 1, fkey) != 1)
        eprintf("Truncated input.\n");
      keysched(&raw, &key);
      wipe(&raw, sizeof raw);
      uint64_t tell = 0;
      cipher_aux_t zero = {
        .type = CIPHER_STREAM_FUNCTION, .max = 0,
        .stream = { zerodev_read, zerodev_write, zerodev_tell, &tell }
      };
      mode_params_t params = {
        .pcb = progress ? progress_callback : NULL,
        .key = key, .input = zero,
        .output = { .type = CIPHER_STREAM_FILE, .file = fout }
      };
      enc(&params);
      break;
    }
    case MODE_ENCODE: {
      if (!fkey) eprintf("No key file specified.\n");
      if (!enc || !dec) eprintf("No mode of operation specified.\n");
      block_key_t raw;  expanded_key_t key;
      if (fread(&raw, sizeof raw, 1, fkey) != 1)
        eprintf("Truncated input.\n");
      keysched(&raw, &key);
      wipe(&raw, sizeof raw);
      mode_params_t params = {
        .pcb = progress ? progress_callback : NULL, .key = key,
        .input = { .type = CIPHER_STREAM_FILE, .file = fin,
                   .max = file_size(fin) },
        .output = { .type = CIPHER_STREAM_FILE, .file = fout }
      };
      enc(&params);
      break;
    }
    case MODE_DECODE: {
      if (!fkey) eprintf("No key file specified.\n");
      if (enc || dec)
        eprintf("Mode of operation needs not specified for decryption.\n");
      block_key_t raw;  expanded_key_t key;
      if (fread(&raw, sizeof raw, 1, fkey) != 1)
        eprintf("Truncated input.\n");
      keysched(&raw, &key);
      wipe(&raw, sizeof raw);
      mode_params_t params = {
        .pcb = progress ? progress_callback : NULL, .key = key,
        .input = { .type = CIPHER_STREAM_FILE, .file = fin,
                   .max = file_size(fin) },
        .output = { .type = CIPHER_STREAM_FILE, .file = fout }
      };
      detect_mode_of_operation(fin, &enc, &dec);
      dec(&params);
      break;
    }
  }
  if (input && fclose(fin))
    eprintf("Could not close `%s': %s\n", input, strerror(errno));
  if (output && fclose(fout))
    eprintf("Could not close `%s': %s\n", output, strerror(errno));
  if (fkey && fclose(fkey))
    eprintf("Could not close key file: %s\n", strerror(errno));
}
