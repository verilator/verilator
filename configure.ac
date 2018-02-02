# DESCRIPTION: Process this file with autoconf to produce a configure script.
#
# Copyright 2003-2018 by Wilson Snyder. Verilator is free software; you can
# redistribute it and/or modify it under the terms of either the GNU Lesser
# General Public License Version 3 or the Perl Artistic License Version 2.0.

#AC_INIT([Verilator],[#.### YYYY-MM-DD])
#AC_INIT([Verilator],[#.### devel])
AC_INIT([Verilator],[3.920 2018-02-01])
# When releasing, also update header of Changes file
# and commit using "devel release" or "Version bump" message

AC_CONFIG_HEADER(src/config_build.h)
AC_CONFIG_FILES(Makefile src/Makefile src/Makefile_obj include/verilated.mk include/verilated_config.h verilator.pc)

AC_MSG_RESULT([configuring for $PACKAGE_STRING])

# Special Substitutions - CFG_WITH_DEFENV
AC_MSG_CHECKING(whether to use hardcoded paths)
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
AC_MSG_RESULT($CFG_WITH_DEFENV)

# Special Substitutions - CFG_WITH_CCWARN
AC_MSG_CHECKING(whether to show and stop on compilation warnings)
AC_ARG_ENABLE([ccwarn],
              [AS_HELP_STRING([--enable-ccwarn],
                              [enable showing and stopping on compilation warnings])],
              [case "${enableval}" in
                yes) CFG_WITH_CCWARN=yes ;;
                no)  CFG_WITH_CCWARN=no ;;
                *)   AC_MSG_ERROR([bad value ${enableval} for --enable-ccwarn]) ;;
               esac],
              [case "x${VERILATOR_AUTHOR_SITE}" in
                x)   CFG_WITH_CCWARN=no ;;
                *)   CFG_WITH_CCWARN=yes ;;
               esac]
              )
AC_SUBST(CFG_WITH_CCWARN)
AC_MSG_RESULT($CFG_WITH_CCWARN)

# Special Substitutions - CFG_WITH_LONGTESTS
AC_MSG_CHECKING(whether to run long tests)
AC_ARG_ENABLE([longtests],
              [AS_HELP_STRING([--enable-longtests],
                              [enable running long developer tests])],
              [case "${enableval}" in
                yes) CFG_WITH_LONGTESTS=yes ;;
                no)  CFG_WITH_LONGTESTS=no ;;
                *)   AC_MSG_ERROR([bad value ${enableval} for --enable-longtests]) ;;
               esac],
              [case "x${VERILATOR_AUTHOR_SITE}" in
                x)   CFG_WITH_LONGTESTS=no ;;
                *)   CFG_WITH_LONGTESTS=yes ;;
               esac]
              )
AC_SUBST(CFG_WITH_LONGTESTS)
AC_MSG_RESULT($CFG_WITH_LONGTESTS)

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

# Checks for typedefs, structures
AC_CHECK_TYPE(size_t,unsigned int)
AC_TYPE_SIZE_T

# Checks for compiler characteristics.
AC_C_INLINE

AC_LINK_IFELSE(
     [AC_LANG_PROGRAM([#include <new>], [[int* a=new int; delete a; ]])],
     [], [AC_MSG_ERROR([$CXX does not seem to successfully compile a simple C++ program])])

AC_DEFUN([_MY_CXX_CHECK_FLAG],
   [# _MY_CXX_CHECK_FLAG(flag) -- Check if compiler supports specific options
    # Set $_my_result appropriately
    ACO_SAVE_CXXFLAGS="$CXXFLAGS"
    # -Werror needed otherwise unknown -Wno-div-by-zero won't report problems
    # new/delete is needed to find -faligned-new link problem on Darwin
    CXXFLAGS="$CXXFLAGS $1 -Werror"
    AC_MSG_CHECKING([whether $CXX accepts $1])
    AC_LINK_IFELSE(
         [AC_LANG_PROGRAM([#include <new>], [[int* a=new int; delete a; ]])],
         [_my_result=yes
          if test -s conftest.err; then
            if grep -e "$1" conftest.err >/dev/null; then
              _my_result=no
            fi
          fi],
         [_my_result=no])
    # GCC is annoying, trying to be helpful, it postpones unknown -Wno-
    # options if there's no error We want to see them regardless, so try
    # forcing an error and see if we get a gcc warning
    AC_COMPILE_IFELSE(
         [AC_LANG_PROGRAM([[an_error "intentional-error-for-test.h"
                          ]],[])],
         [], # Ignore ok exit
         [if test -s conftest.err; then
            if grep -e "$1" conftest.err >/dev/null; then
              _my_result=no
            fi
          fi])
    AC_MSG_RESULT($_my_result)
    CXXFLAGS="$ACO_SAVE_CXXFLAGS"
   ])

AC_DEFUN([_MY_CXX_CHECK_SET],
   [# _MY_CXX_CHECK_SET(variable,flag) -- Check if compiler supports specific options
    # If it does, set variable to flag, only if not previously set
    if test "$$1" = ""; then
       _MY_CXX_CHECK_FLAG($2)
       if test "$_my_result" = "yes" ; then
          $1="$2"
       fi
    fi
   ])

AC_DEFUN([_MY_CXX_CHECK_OPT],
   [# _MY_CXX_CHECK_OPT(flag) -- Check if compiler supports specific options
    # If it does, append flag to variable
    _MY_CXX_CHECK_FLAG($2)
    if test "$_my_result" = "yes" ; then
       $1="$$1 $2"
    fi
   ])

# Flag to select newest language standard supported
# Macros work such that first option that passes is the one we take
# gnu++14 is the newest that Verilator supports
# std++03 is the oldest that Verilator supports
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=gnu++17)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=gnu++14)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=gnu++11)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=gnu++03)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=c++17)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=c++14)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=c++11)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=c++03)
AC_SUBST(CFG_CXXFLAGS_STD_NEWEST)
# And likewise oldest standard (same list above, backwards)
# This is used for internal testing
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=std++03)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=std++11)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=std++14)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=std++17)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=gnu++03)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=gnu++11)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=gnu++14)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=gnu++17)
AC_SUBST(CFG_CXXFLAGS_STD_OLDEST)

# Flags for compiling Verilator internals including parser, and Verilated files
# These turn on extra warnings and are only used with 'configure --enable-ccwarn'
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_WEXTRA,-Wextra)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_WEXTRA,-Wfloat-conversion)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_WEXTRA,-Wlogical-op)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_WEXTRA,-Wthread-safety)
AC_SUBST(CFG_CXXFLAGS_WEXTRA)

# Flags for compiling Verilator internals including parser always
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-Qunused-arguments)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-faligned-new)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-fno-delete-null-pointer-checks)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-Wno-unused-parameter)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-Wno-undefined-bool-conversion)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-Wno-shadow)
AC_SUBST(CFG_CXXFLAGS_SRC)

# Flags for compiling Verilator parser always (in addition to above CFG_CXXFLAGS_SRC)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_PARSER,-Wno-char-subscripts)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_PARSER,-Wno-null-conversion)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_PARSER,-Wno-parentheses-equality)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_PARSER,-Wno-unused)
AC_SUBST(CFG_CXXFLAGS_PARSER)

# Flags for Verilated makefile
# For example, -Wno-div-by-zero isn't in 4.1.2
# Random code often does / 0.  Unfortunately VL_DIV_I(0,0) will warn
# without this flag, even though there's a conditional to prevent the divide.
# We still don't add no-div-by-zero as it throws message to stdout, though doesn't die.
#_MY_CXX_CHECK_OPT(-Wno-div-by-zero)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-faligned-new)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-fbracket-depth=4096)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Qunused-arguments)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-bool-operation)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-parentheses-equality)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-sign-compare)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-uninitialized)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-unused-but-set-variable)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-unused-parameter)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-unused-variable)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-shadow)
AC_SUBST(CFG_CXXFLAGS_NO_UNUSED)

# Set CFG_WITH_THREADED if can support threading
AC_MSG_CHECKING(whether $CXX supports Verilated threads)
ACO_SAVE_CXXFLAGS="$CXXFLAGS"
CXXFLAGS="$CXXFLAGS $CFG_CXXFLAGS_STD_NEWEST $CFG_CXXFLAGS_NO_UNUSED"
AC_LINK_IFELSE(
     [AC_LANG_PROGRAM([#include <thread>], [[ ]])],
     [_my_result=yes
      if test -s conftest.err; then
        if grep -e "$1" conftest.err >/dev/null; then
          _my_result=no
        fi
      fi],
     [_my_result=no])
CFG_WITH_THREADED=$_my_result
AC_SUBST(CFG_WITH_THREADED)
AC_MSG_RESULT($CFG_WITH_THREADED)

# Checks for library functions.
AC_CHECK_MEMBER([struct stat.st_mtim.tv_nsec],
    [AC_DEFINE([HAVE_STAT_NSEC],[1],[Defined if struct stat has st_mtim.tv_nsec])],
    [], [#include <sys/stat.h>])

# Checks for system services

# Other install directories
pkgdatadir=${datadir}/verilator
AC_SUBST(pkgdatadir)
pkgconfigdir=${datadir}/pkgconfig
AC_SUBST(pkgconfigdir)

AC_OUTPUT

AC_MSG_RESULT([])
AC_MSG_RESULT([Now type 'make' (or sometimes 'gmake') to build Verilator.])
AC_MSG_RESULT([])
