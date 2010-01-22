dnl DESCRIPTION: Process this file with autoconf to produce a configure script.
dnl
dnl Copyright 2003-2010 by Wilson Snyder. Verilator is free software; you can
dnl redistribute it and/or modify it under the terms of either the GNU Lesser
dnl General Public License Version 3 or the Perl Artistic License Version 2.0.

AC_INIT(src/Verilator.cpp)
AC_CONFIG_HEADER(src/config_build.h)

dnl Special Substitutions
AC_ARG_ENABLE(defenv,
   [AS_HELP_STRING([--disable-defenv], [disable hardcoded default environment variables])],
   CFG_WITH_DEFENV=$enableval,
   CFG_WITH_DEFENV=yes)
AC_SUBST(CFG_WITH_DEFENV)

dnl Compiler flags
CFLAGS=-I${includedir}
CPPFLAGS=-I${includedir}
CXXFLAGS=-I${includedir}
LDFLAGS=-L${libdir}

dnl Checks for programs.
AC_PROG_CC
AC_PROG_CXX
AC_PROG_INSTALL

AC_LANG_PUSH(C++)
AC_MSG_CHECKING([that C++ compiler can compile simple program])
AC_TRY_RUN([int main() { return 0; }],
           AC_MSG_RESULT(yes),
           AC_MSG_RESULT(no);AC_MSG_ERROR([a working C++ compiler is required]))

AC_PATH_PROG(PERL,perl)
if test "x$PERL" = "x" ; then
   AC_MSG_ERROR([Cannot find "perl" in your PATH, please install it])
fi
AC_PATH_PROG(LEX,flex)
if test "x$LEX" = "x" ; then
   AC_MSG_ERROR([Cannot find "flex" in your PATH, please install it])
fi
AC_PATH_PROG(YACC,bison)
if test "x$YACC" = "x" ; then
   AC_MSG_ERROR([Cannot find "bison" in your PATH, please install it])
fi

dnl Checks for libraries.

dnl Checks for header files.
AC_HEADER_STDC
AC_HEADER_SYS_WAIT
AC_CHECK_HEADERS(fcntl.h unistd.h inttypes.h sys/file.h sys/time.h sys/un.h math.h stdint.h mingw/stdint.h)

dnl Checks for typedefs, structures
AC_CHECK_TYPE(size_t,unsigned int)
AC_CHECK_TYPE(uint_t,unsigned int)
AC_CHECK_TYPE(ulong_t,unsigned long)
AC_TYPE_SIZE_T
AC_STRUCT_TM

dnl Checks for compiler characteristics.
AC_C_INLINE

dnl Checks for library functions.

dnl Checks for system services

dnl Other install directories
pkgdatadir=${datadir}/verilator
AC_SUBST(pkgdatadir)

AC_OUTPUT(Makefile src/Makefile src/Makefile_obj include/verilated.mk)

AC_MSG_RESULT([])
AC_MSG_RESULT([Now type 'gmake'])
AC_MSG_RESULT([])
