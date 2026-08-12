// ---------------------------------------------------------------------------
//      KCrypt - 4th iteration of a cryptographic algorithm.
//      Written on Monday, 3rd of August 2026 by Kamila Szewczyk.
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
//      Constant-time Galois field arithmetic.
// ---------------------------------------------------------------------------
typedef uint8_t gf;
enum {
  KC_BLOCK_SIZE = 64, KC_HALF_SIZE = 32, KC_NONCE_SIZE = 16, KC_ROUNDS = 16
};
/*  Optimisation barrier.  */
#if !defined(HAVE_ASM_BARRIER) && (defined(__GNUC__) || defined(__clang__))
  #define HAVE_ASM_BARRIER 1
#endif
#ifdef HAVE_ASM_BARRIER
static gf gf_opaque(gf value) {
  __asm__ volatile ("" : "+r" (value));  return value;
}
#else
static gf gf_opaque(gf value) {
  volatile gf laundered = value;  return laundered;
}
#endif
static void wipe(void * buffer, size_t length) {
  volatile gf * target = buffer;
  while (length--)
    *target++ = 0;
  #ifdef HAVE_ASM_BARRIER
    __asm__ volatile ("" : : : "memory");
  #endif
}
/*  All ones when the arguments are equal, all zeroes otherwise.  */
static gf gf_eq(gf a, gf b) {
  return gf_opaque((gf) (((uint32_t) (gf) (a ^ b) - 1) >> 8));
}
static gf gf_mul2(gf value) {
  gf carry = gf_opaque((gf) -(gf) (value >> 7));
  return (gf) ((unsigned int) value << 1) ^ (carry & 0x1d);
}
static gf gf_mul(gf a, gf b) {
  gf product = 0;
  for (int i = 0; i < 8; i++) {
    product ^= a & gf_opaque((gf) -(gf) (b & 1));
    b >>= 1;  a = gf_mul2(a);
  }
  return product;
}
/*  The multiplicative inverse is value^254, reached by an addition chain.  */
static gf gf_inv(gf value) {
  gf square = gf_mul(value, value);
  gf cube = gf_mul(square, value);
  gf sixth = gf_mul(cube, cube);
  gf twelfth = gf_mul(sixth, sixth);
  gf accumulator = gf_mul(twelfth, cube);           /* value^15  */
  for (int i = 0; i < 4; i++)
    accumulator = gf_mul(accumulator, accumulator); /* value^240 */
  return gf_mul(gf_mul(accumulator, twelfth), square);
}
/*  Remainder by bitwise long division.  */
static gf gf_mod(gf value, gf modulus) {
  uint32_t remainder = 0;
  for (int i = 7; i >= 0; i--) {
    remainder += remainder + ((value >> i) & 1);
    uint32_t borrowed = remainder - modulus;
    gf underflow = gf_opaque((gf) -(gf) (borrowed >> 31));
    remainder = borrowed + (modulus & underflow);
  }
  return (gf) remainder;
}

// ---------------------------------------------------------------------------
//      Feistel Network.
// ---------------------------------------------------------------------------
typedef struct { gf k1[32]; gf k2[64]; } block_key_t;
typedef struct {
  gf k2[64];
  gf round[16][32];
  gf permutation[16][32];
} expanded_key_t;

/*  A Fisher-Yates shuffle whose exchange is applied as a masked swap against
    every position, so the addresses touched do not reveal the key. */
static void fisher32(const gf k[64], gf x[32], int round) {
  for (int i = 0; i < 32; i++) x[i] = (gf) i;
  for (int i = 31; i > 0; i--) {
    gf j = gf_mod(k[(i + round * 21) & 63], (gf) (i + 1));
    for (int q = 0; q < 32; q++) {
      gf t = (gf) (x[i] ^ x[q]) & gf_eq((gf) q, j);
      x[i] ^= t; x[q] ^= t;
    }
  }
}
/*  out[i] = in[permutation[i]], read as a masked scan over the input.  */
static void permute32(gf out[32], const gf in[32], const gf permutation[32]) {
  for (int i = 0; i < 32; i++) {
    gf gathered = 0;
    for (int q = 0; q < 32; q++)
      gathered |= in[q] & gf_eq((gf) q, permutation[i]);
    out[i] = gathered;
  }
}
static void diffuse32(gf value[32]) {
  static const unsigned int offsets[] = { 1, 3, 7, 13 };
  gf next[32];
  for (size_t layer = 0;
      layer < sizeof(offsets) / sizeof(offsets[0]); layer++) {
    for (int i = 0; i < 32; i++)
      next[i] = value[i] ^ gf_mul2(value[(i + offsets[layer]) & 31]);
    memcpy(value, next, sizeof(next));
  }
  wipe(next, sizeof(next));
}
/*  The round permutations depend only on the key, so they are derived once
    here rather than being rebuilt for every block that gets encrypted.  */
static void keysched(const block_key_t * key, expanded_key_t * expanded) {
  gf state[32], next[32], permuted[32];
  memcpy(state, key->k1, sizeof(state));
  memcpy(expanded->k2, key->k2, sizeof(expanded->k2));
  for (int round = 0; round < KC_ROUNDS; round++) {
    fisher32(expanded->k2, expanded->permutation[round], round);
    permute32(permuted, state, expanded->permutation[round]);
    for (int i = 0; i < 32; i++) {
      gf mixed = permuted[i]
        ^ gf_mul2(permuted[(i + 1) & 31])
        ^ expanded->k2[(i + round * 17) & 63]
        ^ (gf) ((round + 1) * 0x9d + i);
      next[i] = (gf) ((unsigned int) gf_inv(mixed)
        + expanded->k2[(i + 32 + round * 29) & 63]);
    }
    diffuse32(next);
    memcpy(expanded->round[round], next, sizeof(next));
    memcpy(state, next, sizeof(state));
  }
  wipe(state, sizeof(state));
  wipe(next, sizeof(next));
  wipe(permuted, sizeof(permuted));
}
static void feistelF(gf b[32], const gf round_key[32],
    const gf permutation_key[64], const gf permutation[32], int round) {
  gf permuted[32];
  permute32(permuted, b, permutation);
  for (int i = 0; i < 32; i++) {
    gf mixed = permuted[i]
      ^ gf_mul2(permuted[(i + 1) & 31])
      ^ permutation_key[(i + 32 + round * 11) & 63];
    b[i] = (gf) ((unsigned int) round_key[i] + gf_inv(mixed));
  }
  diffuse32(b);
  wipe(permuted, sizeof(permuted));
}
static void feistel0(gf L[32], gf R[32], const expanded_key_t * key) {
  gf temp[32];
  for (int round = 0; round < KC_ROUNDS; round++) {
    memcpy(temp, R, sizeof(temp));
    feistelF(R, key->round[round], key->k2,
      key->permutation[round], round);
    for (int i = 0; i < 32; i++) R[i] ^= L[i];
    memcpy(L, temp, sizeof(temp));
  }
  wipe(temp, sizeof(temp));
}
static void encode_block(const gf in[64], gf blk[64],
    const expanded_key_t * key) {
  memcpy(blk, in, 64);
  feistel0(blk, blk + 32, key);
}

// ---------------------------------------------------------------------------
//      Secure randomness source. Supports `dows, DOS and Unix systems.
// ---------------------------------------------------------------------------
static void eprintf(const char * fmt, ...) {
  va_list args;
  va_start(args, fmt);
  vfprintf(stderr, fmt, args);
  va_end(args);
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
  gf * output = buf;
  while (len > 0) {
    ssize_t amount = read(fd, output, len);
    if (amount < 0 && errno == EINTR)
      continue;
    if (amount <= 0) {
      int saved_errno = errno;
      close(fd);
      if (amount == 0)
        eprintf("Could not read from `/dev/urandom': unexpected EOF.\n");
      eprintf("Could not read from `/dev/urandom': %s\n",
        strerror(saved_errno));
    }
    output += (size_t) amount;
    len -= (size_t) amount;
  }
  if (close(fd) < 0)
    eprintf("Could not close `/dev/urandom': %s\n", strerror(errno));
}
#elif __MSDOS__
static void secrandom(void * buf, size_t len) { // Doug Kaufman's NOISE.SYS
  FILE * f = fopen("/dev/urandom$", "rb");
  if (!f)
    eprintf("Could not open `/dev/urandom$': %s\n", strerror(errno));
  if (fread(buf, 1, len, f) < len)
    eprintf("Could not read from `/dev/urandom$': %s\n", strerror(errno));
  fclose(f);
}
#endif

// ---------------------------------------------------------------------------
//      Stream ciphers.
// ---------------------------------------------------------------------------
enum { CIPHER_STREAM_FILE, CIPHER_STREAM_BLOCK, CIPHER_STREAM_FUNCTION };
typedef struct {
  int type;
  uint64_t max;
  union {
    FILE * file;
    struct {
      size_t (* read)(void * ptr, size_t size, size_t nmemb, void * stream);
      size_t (* write)(const void * ptr, size_t size, size_t nmemb, void * stream);
      uint64_t (* tell)(void * stream);
      void * stream;
    } stream;
    struct {
      uint8_t * buffer;
      size_t size, consumed;
    };
  };
} cipher_aux_t;
static void write64_le_buf(uint64_t value, gf buffer[8]) {
  for (int i = 0; i < 8; i++)
    buffer[i] = (gf) (value >> (i * 8));
}
static size_t cipher_aux_fread(void * ptr, size_t size,
    size_t nmemb, cipher_aux_t * stream) {
  if (stream->type == CIPHER_STREAM_FILE) {
    size_t amount = fread(ptr, size, nmemb, stream->file);
    if (amount < nmemb && ferror(stream->file))
      eprintf("Could not read from the input file: %s\n", strerror(errno));
    return amount;
  } else if (stream->type == CIPHER_STREAM_FUNCTION) {
    return stream->stream.read(ptr, size, nmemb, stream->stream.stream);
  }
  if (stream->consumed + size * nmemb > stream->size)
    eprintf("Internal error.\n");
  memcpy(ptr, stream->buffer + stream->consumed, size * nmemb);
  stream->consumed += size * nmemb;
  return nmemb;
}
static size_t cipher_aux_fwrite(const void * ptr, size_t size,
    size_t nmemb, cipher_aux_t * stream) {
  if (nmemb == 0 || size == 0)
    return 0;
  if (stream->type == CIPHER_STREAM_FILE) {
    if(fwrite(ptr, size, nmemb, stream->file) != nmemb)
      eprintf("Could not write to the output file: %s\n", strerror(errno));
    return nmemb;
  }
  else if (stream->type == CIPHER_STREAM_FUNCTION)
    return stream->stream.write(ptr, size, nmemb, stream->stream.stream);
  if (stream->consumed + size * nmemb > stream->size)
    eprintf("Internal error.\n");
  memcpy(stream->buffer + stream->consumed, ptr, size * nmemb);
  stream->consumed += size * nmemb;
  return nmemb;
}
static uint64_t cipher_aux_ftell(cipher_aux_t * stream) {
  if (stream->type == CIPHER_STREAM_FILE) {
    long position = ftell(stream->file);
    return position < 0 ? 0 : (uint64_t) position;
  }
  else if (stream->type == CIPHER_STREAM_FUNCTION)
    return stream->stream.tell(stream->stream.stream);
  return stream->consumed;
}

typedef void (* fprogress_cb)(uint64_t processed, uint64_t total);
typedef struct {
  fprogress_cb pcb;
  expanded_key_t key;
  cipher_aux_t input, output;
} mode_params_t;

typedef void (* stream_enc)(mode_params_t * params);
typedef void (* stream_dec)(mode_params_t * params);

static void cipher_check_header(mode_params_t * params,
    gf nonce[KC_NONCE_SIZE]) {
  if (cipher_aux_fread(nonce, 1, KC_NONCE_SIZE, &params->input)
      != KC_NONCE_SIZE)
    eprintf("Truncated input.\n");
}
static void cipher_put_header(const char * hdr, mode_params_t * params,
    gf nonce[KC_NONCE_SIZE]) {
  size_t hdr_len = strlen(hdr);
  gf actual_hdr[6 + KC_NONCE_SIZE];
  if (hdr_len != 6)
    eprintf("Internal error: invalid ciphertext header.\n");
  memcpy(actual_hdr, hdr, hdr_len);
  secrandom(nonce, KC_NONCE_SIZE);
  memcpy(actual_hdr + hdr_len, nonce, KC_NONCE_SIZE);
  cipher_aux_fwrite(actual_hdr, 1, sizeof(actual_hdr), &params->output);
}

// ---------------------------------------------------------------------------
//      Standard length-preserving CTR and OFB modes.
// ---------------------------------------------------------------------------
static void crypt_ctr(mode_params_t * params, int encode) {
  gf nonce[KC_NONCE_SIZE], input[KC_BLOCK_SIZE], output[KC_BLOCK_SIZE];
  gf counter_block[KC_BLOCK_SIZE] = { 0 }, key_stream[KC_BLOCK_SIZE];
  uint64_t counter = 0;

  if (encode)
    cipher_put_header("KC4CTR", params, nonce);
  else
    cipher_check_header(params, nonce);
  memcpy(counter_block, nonce, sizeof(nonce));
  counter_block[KC_BLOCK_SIZE - 1] = 1; /* Mode-domain separator. */

  size_t amount;
  while ((amount = cipher_aux_fread(input, 1, sizeof(input),
      &params->input)) > 0) {
    write64_le_buf(counter, counter_block + KC_NONCE_SIZE);
    encode_block(counter_block, key_stream, &params->key);
    for (size_t i = 0; i < amount; i++)
      output[i] = input[i] ^ key_stream[i];
    cipher_aux_fwrite(output, 1, amount, &params->output);
    if (params->pcb)
      params->pcb(cipher_aux_ftell(&params->input), params->input.max);
    if (counter == UINT64_MAX)
      eprintf("Input is too large for CTR mode.\n");
    counter++;
  }
}

static void encode_ctr(mode_params_t * params) { crypt_ctr(params, 1); }
static void decode_ctr(mode_params_t * params) { crypt_ctr(params, 0); }

static void crypt_ofb(mode_params_t * params, int encode) {
  gf nonce[KC_NONCE_SIZE], input[KC_BLOCK_SIZE], output[KC_BLOCK_SIZE];
  gf state[KC_BLOCK_SIZE] = { 0 }, next[KC_BLOCK_SIZE];

  if (encode)
    cipher_put_header("KC4OFB", params, nonce);
  else
    cipher_check_header(params, nonce);
  memcpy(state, nonce, sizeof(nonce));
  state[KC_BLOCK_SIZE - 1] = 2; /* Mode-domain separator. */

  size_t amount;
  while ((amount = cipher_aux_fread(input, 1, sizeof(input),
      &params->input)) > 0) {
    encode_block(state, next, &params->key);
    memcpy(state, next, sizeof(state));
    for (size_t i = 0; i < amount; i++)
      output[i] = input[i] ^ state[i];
    cipher_aux_fwrite(output, 1, amount, &params->output);
    if (params->pcb)
      params->pcb(cipher_aux_ftell(&params->input), params->input.max);
  }
}

static void encode_ofb(mode_params_t * params) { crypt_ofb(params, 1); }
static void decode_ofb(mode_params_t * params) { crypt_ofb(params, 0); }

// ---------------------------------------------------------------------------
//      Command-line stub.
// ---------------------------------------------------------------------------
enum { MODE_ENCODE, MODE_DECODE, MODE_KEYGEN, MODE_RANDOM };

static uint64_t file_size(FILE * file) {
  long original = ftell(file);
  if (original < 0 || fseek(file, 0, SEEK_END) != 0) {
    clearerr(file);
    return 0;
  }
  long end = ftell(file);
  if (fseek(file, original, SEEK_SET) != 0 || end < 0) {
    clearerr(file);
    return 0;
  }
  return (uint64_t) end;
}

static void detect_mode_of_operation(FILE * ciphertext,
    stream_enc * e, stream_dec * d) {
  char hdr[6];
  if (fread(hdr, 1, 6, ciphertext) != 6)
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

static void progress_callback(uint64_t processed, uint64_t total) {
  if ((processed % 8192) == 0) {
    processed /= 1024; total /= 1024;
    if (total == 0)
      fprintf(stderr, "\rProcessed: %" PRIu64 "kB.", processed);
    else
      fprintf(stderr, "\rProcessed: %" PRIu64 "/%" PRIu64 "kB.",
        processed, total);
  }
}

static size_t zerodev_read(void * ptr, size_t size,
    size_t nmemb, void * stream) {
  memset(ptr, 0, size * nmemb);
  *((uint64_t *) stream) += size * nmemb;
  return nmemb;
}
static size_t zerodev_write(const void * ptr, size_t size,
    size_t nmemb, void * stream) {
  (void) ptr;  (void) size;  (void) stream;  return nmemb;
}
static uint64_t zerodev_tell(void * stream) {
  return *((uint64_t *) stream);
}

int main(int argc, char * argv[]) {
  yarg_options opt[] = {
    // Actions
    { 'e', no_argument, "encode" },
    { 'd', no_argument, "decode" },
    { 'g', no_argument, "genkey" },
    { 'r', no_argument, "random" },
    // General
    { 'v', no_argument, "version" },
    { 'p', no_argument, "progress" },
    { 'h', no_argument, "help" },
    { 'c', no_argument, "stdout" },
    { 'f', no_argument, "force" },
    { 'm', required_argument, "mode" },
    { 'k', required_argument, "key" },
    { 0, 0, 0 }
  };
  yarg_settings settings = {
    .dash_dash = 1, .style = YARG_STYLE_UNIX
  };
  yarg_result * res = yarg_parse(argc, argv, opt, settings);
  if (!res) eprintf("Out of memory.\n");
  if (res->error)
    eprintf("%s\nTry `kcrypt --help' for more information.\n", res->error);
  int mode = -1, force = 0, progress = 0, force_stdout = 0;
  stream_enc enc = NULL; stream_dec dec = NULL;
  const char * key_path = NULL;
  for (int i = 0; i < res->argc; i++) {
    switch(res->args[i].opt) {
      case 'e': mode = MODE_ENCODE; break;
      case 'd': mode = MODE_DECODE; break;
      case 'g': mode = MODE_KEYGEN; break;
      case 'r': mode = MODE_RANDOM; break;
      case 'f': force = 1; break;
      case 'h': help(); return 0;
      case 'v': version(); return 0;
      case 'p': progress = 1; break;
      case 'c': force_stdout = 1; break;
      case 'k': key_path = res->args[i].arg; break;
      case 'm':
        for (char * p = res->args[i].arg; *p; p++)
          *p = (char) tolower((unsigned char) *p);
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
            "Try `kcrypt3 --help' for more information.\n");
  #if defined(__MSVCRT__)
    setmode(STDIN_FILENO, O_BINARY);
    setmode(STDOUT_FILENO, O_BINARY);
  #endif
  char * f1 = NULL, * f2 = NULL;
  for (int i = 0; i < res->pos_argc; i++) {
    char * arg = res->pos_args[i];
    if (f1 != NULL && f2 != NULL)
      eprintf("Too many positional arguments.\n");
    if (f1 == NULL) f1 = arg; else f2 = arg;
  }
  char * input = NULL, * output = NULL;
  if (f1 != NULL || f2 != NULL) {
    if (mode == MODE_ENCODE) {
      if (f2 == NULL) {
        input = f1;
        if (!force_stdout) {
          output = malloc(strlen(f1) + 5);
          strcpy(output, f1);
          strcat(output, ".kc4");
        }
      } else { input = f1, output = f2; }
    } else if (mode == MODE_DECODE) {
      if (f2 == NULL) {
        input = f1;
        if(!force_stdout) {
          output = malloc(strlen(f1) + 1);
          strcpy(output, f1);
          if (strlen(f1) > 4 && !strcmp(f1 + strlen(f1) - 4, ".kc4"))
            output[strlen(f1) - 4] = 0;
          else
            eprintf("File `%s' has an unrecognised extension.\n", f1);
        }
      } else { input = f1, output = f2; }
    } else if (mode == MODE_RANDOM) {
      output = f1;
      if (f2 != NULL)
        eprintf("Too many positional arguments.\n");
    } else if (mode == MODE_KEYGEN) {
      if (f1 != NULL || f2 != NULL)
        eprintf("Too many positional arguments.\n");
    }
  }
  FILE * in_file = stdin, * out_file = stdout, * key_file = NULL;
  if (input != NULL) {
    in_file = fopen(input, "rb");
    if (!in_file)
      eprintf("Could not open `%s': %s\n", input, strerror(errno));
  }
  if (key_path != NULL) {
    #if defined(__unix__)
    if (mode == MODE_KEYGEN) {
      int key_fd = open(key_path, O_WRONLY | O_CREAT | O_TRUNC, 0600);
      if (key_fd >= 0)
        key_file = fdopen(key_fd, "wb");
      if (key_fd >= 0 && !key_file)
        close(key_fd);
    } else
      key_file = fopen(key_path, "rb");
    #else
    key_file = fopen(key_path, mode == MODE_KEYGEN ? "wb" : "rb");
    #endif
    if (!key_file)
      eprintf("Could not open `%s': %s\n", key_path, strerror(errno));
  }
  if (output && !force && access(output, F_OK) == 0)
    eprintf("File `%s' already exists. Use `-f' to overwrite.\n", output);
  if (output != NULL) {
    out_file = fopen(output, "wb");
    if (!out_file)
      eprintf("Could not open `%s': %s\n", output, strerror(errno));
  }
  switch(mode) {
    case MODE_KEYGEN: {
      if (!key_file) eprintf("No key file specified.\n");
      block_key_t k; secrandom(&k, sizeof(k));
      int written = fwrite(&k, sizeof(k), 1, key_file) == 1;
      wipe(&k, sizeof(k));
      if (!written)
        eprintf("Could not write to key file: %s\n", strerror(errno));
      break;
    }
    case MODE_RANDOM: {
      if (!key_file) eprintf("No key file specified.\n");
      if (!enc || !dec)
        eprintf("No mode of operation specified.\n");
      block_key_t raw_key;
      expanded_key_t key;
      if (fread(&raw_key, sizeof(raw_key), 1, key_file) != 1)
        eprintf("Truncated input.\n");
      keysched(&raw_key, &key);
      wipe(&raw_key, sizeof(raw_key));
      uint64_t zero_tell = 0;
      cipher_aux_t zero_device = {
        .type = CIPHER_STREAM_FUNCTION, .max = 0,
        .stream = { zerodev_read, zerodev_write, zerodev_tell, &zero_tell }
      };
      mode_params_t params = {
        .pcb = progress ? progress_callback : NULL,
        .key = key, .input = zero_device, .output = {
          .type = CIPHER_STREAM_FILE, .file = out_file
        }
      };
      enc(&params);
      break;
    }
    case MODE_ENCODE: {
      if (!key_file) eprintf("No key file specified.\n");
      if (!enc || !dec)
        eprintf("No mode of operation specified.\n");
      block_key_t raw_key;
      expanded_key_t key;
      if (fread(&raw_key, sizeof(raw_key), 1, key_file) != 1)
        eprintf("Truncated input.\n");
      keysched(&raw_key, &key);
      wipe(&raw_key, sizeof(raw_key));
      cipher_aux_t input = {
        .type = CIPHER_STREAM_FILE, .file = in_file, .max = file_size(in_file)
      };
      cipher_aux_t output = {
        .type = CIPHER_STREAM_FILE, .file = out_file
      };
      mode_params_t params = {
        .pcb = progress ? progress_callback : NULL,
        .key = key, .input = input, .output = output
      };
      enc(&params);
      break;
    }
    case MODE_DECODE: {
      if (!key_file) eprintf("No key file specified.\n");
      if (enc || dec)
        eprintf("Mode of operation needs not specified for decryption.\n");
      block_key_t raw_key;
      expanded_key_t key;
      if (fread(&raw_key, sizeof(raw_key), 1, key_file) != 1)
        eprintf("Truncated input.\n");
      keysched(&raw_key, &key);
      wipe(&raw_key, sizeof(raw_key));
      cipher_aux_t input = {
        .type = CIPHER_STREAM_FILE, .file = in_file, .max = file_size(in_file)
      };
      cipher_aux_t output = {
        .type = CIPHER_STREAM_FILE, .file = out_file
      };
      mode_params_t params = {
        .pcb = progress ? progress_callback : NULL,
        .key = key, .input = input, .output = output
      };
      detect_mode_of_operation(in_file, &enc, &dec);
      dec(&params);
      break;
    }
  }
  if (input != NULL && fclose(in_file) != 0)
    eprintf("Could not close `%s': %s\n", input, strerror(errno));
  if (output != NULL && fclose(out_file) != 0)
    eprintf("Could not close `%s': %s\n", output, strerror(errno));
  if (key_file != NULL && fclose(key_file) != 0)
    eprintf("Could not close key file: %s\n", strerror(errno));
}
