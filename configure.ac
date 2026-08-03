AC_PREREQ([2.69])
AC_INIT([kcrypt],[1.0.0],[https://github.com/iczelia/kcrypt])
AC_CONFIG_HEADERS([config.h])
AC_COPYRIGHT([Released to the public domain by Kamila Szewczyk])
AC_LANG([C])
AC_CONFIG_MACRO_DIR([m4])

AC_CANONICAL_TARGET
AM_INIT_AUTOMAKE([-Wall color-tests foreign])

AC_PROG_INSTALL
AC_PROG_MAKE_SET
AC_PROG_CC

AC_CHECK_HEADERS([io.h])
AC_CHECK_FUNCS([_setmode])

AC_CHECK_SIZEOF([size_t])

AC_ARG_ENABLE([native], [AS_HELP_STRING([--enable-native], [Enable native platform optimisations.])], [enable_native=$enableval], [enable_native=no])
if test "x$enable_native" = "xyes"; then
  AX_APPEND_COMPILE_FLAGS([-march=native -mtune=native])
fi

AC_ARG_ENABLE([static], [AS_HELP_STRING([--enable-static], [Enable static linking.])], [enable_static=$enableval], [enable_static=no])
if test "x$enable_static" = "xyes"; then
  AX_APPEND_LINK_FLAGS([-static])
fi

AC_ARG_ENABLE([lto], [AS_HELP_STRING([--enable-lto], [Enable link-time optimisation.])], [enable_lto=$enableval], [enable_lto=no])
if test "x$enable_lto" = "xyes"; then
  AX_APPEND_COMPILE_FLAGS([-flto])
  AX_APPEND_LINK_FLAGS([-flto])
fi

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
