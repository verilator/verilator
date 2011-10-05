# DESCRIPTION: Process this file with autoconf to produce a configure script.
#
# Copyright 2003-2011 by Wilson Snyder. Verilator is free software; you can
# redistribute it and/or modify it under the terms of either the GNU Lesser
# General Public License Version 3 or the Perl Artistic License Version 2.0.

AC_INIT([Verilator],[3.822 devel])
AC_CONFIG_HEADER(src/config_build.h)
AC_CONFIG_FILES(Makefile src/Makefile src/Makefile_obj include/verilated.mk)

AC_MSG_RESULT([configuring for $PACKAGE_STRING])

# Special Substitutions
AC_ARG_ENABLE([defenv],
              [AS_HELP_STRING([--disable-defenv],
                              [disable using some hardcoded data paths extracted from some default environment variables (the default is to use hardcoded paths)])],
              [case "${enableval}" in
                yes) CFG_WITH_DEFENV=yes ;;
                no)  CFG_WITH_DEFENV=no ;;
                *)   AC_MSG_ERROR([bad value ${enableval} for --disable-defenv]) ;;
               esac],
              CFG_WITH_DEFENV=yes)
AC_SUBST(CFG_WITH_DEFENV)

# Compiler flags
CFLAGS=-I${includedir}
CPPFLAGS=-I${includedir}
CXXFLAGS=-I${includedir}
LDFLAGS=-L${libdir}

# Checks for programs.
AC_PROG_CC
AC_PROG_CXX
AC_PROG_INSTALL

AC_LANG_PUSH(C++)
AC_MSG_CHECKING([that C++ compiler can compile simple program])
AC_RUN_IFELSE(
           [AC_LANG_SOURCE([int main() { return 0; }])],
           AC_MSG_RESULT(yes),
           AC_MSG_RESULT(no);AC_MSG_ERROR([a working C++ compiler is required]),
	   AC_MSG_RESULT(yes))

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

# Checks for libraries.

# Checks for header files.
AC_HEADER_STDC
AC_HEADER_SYS_WAIT
AC_CHECK_HEADERS(fcntl.h unistd.h inttypes.h sys/file.h sys/time.h sys/un.h math.h stdint.h mingw/stdint.h)

# Checks for typedefs, structures
AC_CHECK_TYPE(size_t,unsigned int)
AC_CHECK_TYPE(uint_t,unsigned int)
AC_CHECK_TYPE(ulong_t,unsigned long)
AC_TYPE_SIZE_T
AC_STRUCT_TM

# Checks for compiler characteristics.
AC_C_INLINE

# Checks for library functions.

# Checks for system services

# Other install directories
pkgdatadir=${datadir}/verilator
AC_SUBST(pkgdatadir)

AC_OUTPUT

AC_MSG_RESULT([])
AC_MSG_RESULT([Now type 'make' (or sometimes 'gmake') to build Verilator.])
AC_MSG_RESULT([])
