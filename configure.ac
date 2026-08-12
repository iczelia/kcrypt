AC_PREREQ([2.69])
AC_INIT([kcrypt],[1.0.0],[https://github.com/iczelia/kcrypt])
AC_CONFIG_HEADERS([config.h])
AC_COPYRIGHT([Released to the public domain by Kamila Szewczyk])
AC_LANG([C])

AC_CANONICAL_TARGET
AM_INIT_AUTOMAKE([-Wall color-tests foreign])

AC_PROG_INSTALL
AC_PROG_MAKE_SET
AC_PROG_CC

AC_CHECK_HEADERS([io.h])
AC_CHECK_FUNCS([_setmode])

AC_CHECK_SIZEOF([size_t])

AC_CACHE_CHECK([for a GCC-style optimisation barrier], [kc_cv_asm_barrier],
  [AC_LINK_IFELSE(
    [AC_LANG_PROGRAM(
      [[static unsigned char launder(unsigned char v) {
          __asm__ volatile ("" : "+r" (v));
          return v;
        }]],
      [[unsigned char v = launder(0x5a);
        __asm__ volatile ("" : : : "memory");
        return v == 0x5a ? 0 : 1;]])],
    [kc_cv_asm_barrier=yes],
    [kc_cv_asm_barrier=no])])
if test "x$kc_cv_asm_barrier" = "xyes"; then
  AC_DEFINE([HAVE_ASM_BARRIER], [1],
    [Define to 1 if the compiler accepts a GCC-style optimisation barrier.])
else
  AC_MSG_WARN([no optimisation barrier is available: the constant-time cipher
core will fall back to `volatile', which the compiler is free to weaken.])
fi

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
