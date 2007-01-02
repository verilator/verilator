dnl $Id$
dnl DESCRIPTION: Process this file with autoconf to produce a configure script.
dnl Copyright 2003-2007 by Wilson Snyder. This program is free software; you can
dnl redistribute it and/or modify it under the terms of either the GNU
dnl General Public License or the Perl Artistic License.

AC_REVISION($Revision$)dnl
AC_INIT(src/Verilator.cpp)
AC_CONFIG_HEADER(src/config_build.h)

dnl Special Substitutions

dnl Checks for programs.
CXX=g++
AC_PROG_CC
AC_PROG_CXX
AC_PROG_INSTALL
AC_PATH_PROG(PERL,perl)
AC_PATH_PROG(YACC,bison)
AC_PATH_PROG(LEX,flex)

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
AC_MSG_RESULT([Now type 'make'])
AC_MSG_RESULT([])
