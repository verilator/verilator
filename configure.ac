# DESCRIPTION: Process this file with autoconf to produce a configure script.
#
# Copyright 2003-2020 by Wilson Snyder. Verilator is free software; you
# can redistribute it and/or modify it under the terms of either the GNU Lesser
# General Public License Version 3 or the Perl Artistic License Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#AC_INIT([Verilator],[#.### YYYY-MM-DD])
#AC_INIT([Verilator],[#.### devel])
AC_INIT([Verilator],[4.031 devel],
        [https://verilator.org],
        [verilator],[https://verilator.org])
# When releasing, also update header of Changes file
# and commit using "devel release" or "Version bump" message

AC_CONFIG_HEADER(src/config_build.h)
AC_CONFIG_FILES(Makefile docs/Makefile src/Makefile src/Makefile_obj include/verilated.mk include/verilated_config.h verilator.pc verilator-config.cmake verilator-config-version.cmake)

AC_MSG_RESULT([configuring for $PACKAGE_STRING])

# Ignore automake flags passed by Ubuntu builds
AC_ARG_ENABLE([dependency-tracking],
              [AS_HELP_STRING([--disable-dependency-tracking], [ignored])])
AC_ARG_ENABLE([maintainer-mode],
              [AS_HELP_STRING([--enable-maintainer-mode], [ignored])])
AC_ARG_ENABLE([silent-rules],
              [AS_HELP_STRING([--disable-silent-rules], [ignored])])

# Flag to enable linking specific libraries statically
AC_MSG_CHECKING(whether to perform partial static linking of Verilator binary)
AC_ARG_ENABLE([partial-static],
              [AS_HELP_STRING([--disable-partial-static],
                              [By default, for Verilation peformance, Verilator
                               is linked against some of its dependencies
                               statically. Use this to link the Verilator binary
                               fully dynamically.])],
              [case "${enableval}" in
                yes) CFG_ENABLE_PARTIAL_STATIC=yes ;;
                no)  CFG_ENABLE_PARTIAL_STATIC=no ;;
                *)   AC_MSG_ERROR([bad value '${enableval}' for --disable-partial-static]) ;;
               esac],
               CFG_ENABLE_PARTIAL_STATIC=yes)
AC_MSG_RESULT($CFG_ENABLE_PARTIAL_STATIC)

# Flag to enable linking Verilator with tcmalloc if available
AC_MSG_CHECKING(whether to use tcmalloc)
AC_ARG_ENABLE([tcmalloc],
              [AS_HELP_STRING([--enable-tcmalloc],
                              [Use libtcmalloc_minimal for faster dynamic memory
                               management in Verilator binary@<:@default=check@:>@])],
              [case "${enableval}" in
                yes) CFG_WITH_TCMALLOC=yes ;;
                no)  CFG_WITH_TCMALLOC=no ;;
                *)   AC_MSG_ERROR([bad value '${enableval}' for --enable-tcmalloc]) ;;
               esac],
              [CFG_WITH_TCMALLOC=check;])
AC_MSG_RESULT($CFG_WITH_TCMALLOC)

# Special Substitutions - CFG_WITH_DEFENV
AC_MSG_CHECKING(whether to use hardcoded paths)
AC_ARG_ENABLE([defenv],
              [AS_HELP_STRING([--disable-defenv],
                              [disable using some hardcoded data paths extracted
                              from some default environment variables (the default
                              is to use hardcoded paths) in Verilator binary])],
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
                              [enable showing and stopping on compilation warnings
                               in Verilator binrary and Verilated makefiles])],
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

# CFG_WITH_PREC11
AC_MSG_CHECKING(whether allow pre-C++11)
AC_ARG_ENABLE([prec11],
              [AS_HELP_STRING([--enable-prec11],
                              [enable pre-C++11 compilers for Verilator binary
                               and Verilated makefiles])],
              [case "${enableval}" in
                yes) CFG_WITH_PREC11=yes ;;
                no)  CFG_WITH_PREC11=no ;;
                *)   AC_MSG_ERROR([bad value ${enableval} for --enable-prec11]) ;;
               esac],
              [CFG_WITH_PREC11=no;]
              )
AC_SUBST(CFG_WITH_PREC11)
AC_MSG_RESULT($CFG_WITH_PREC11)

# Compiler flags
CFLAGS+=" -I${includedir}"
CPPFLAGS+=" -I${includedir}"
CXXFLAGS+=" -I${includedir}"
LDFLAGS+=" -L${libdir}"

# Checks for programs.
AC_PROG_CC
AC_PROG_CXX
AC_PROG_INSTALL

AC_LANG_PUSH(C++)
cxx_version=$($CXX --version | head -1)
AC_MSG_RESULT([compiler is $CXX --version = $cxx_version])
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

AC_DEFUN([_MY_LDLIBS_CHECK_FLAG],
   [# _MY_LDLIBS_CHECK_FLAG(flag) -- Check if linker supports specific options
    # Set $_my_result appropriately
    ACO_SAVE_LIBS="$LIBS"
    LIBS="$LIBS $1"
    AC_MSG_CHECKING([whether $CXX linker accepts $1])
    AC_LINK_IFELSE(
         [AC_LANG_PROGRAM([[]])],
         [_my_result=yes
          if test -s conftest.err; then
            if grep -e "$1" conftest.err >/dev/null; then
              _my_result=no
            fi
          fi],
         [_my_result=no])
    AC_MSG_RESULT($_my_result)
    LIBS="$ACO_SAVE_LIBS"
   ])

AC_DEFUN([_MY_LDLIBS_CHECK_IFELSE],
   [# _MY_LDLIBS_CHECK_IFELSE(flag,action-if-supported,action-if-not-supported)
    # Check if linker supports specific flag, if it does do action-if-supported
    # otherwise do action-if-not-supported
    _MY_LDLIBS_CHECK_FLAG($1)
    if test "$_my_result" = "yes" ; then
      true
      $2
    else
      true
      $3
    fi
   ])

AC_DEFUN([_MY_LDLIBS_CHECK_OPT],
   [# _MY_LDLIBS_CHECK_OPT(variable, flag) -- Check if linker supports specific
    # options. If it does, append flag to variable.
    _MY_LDLIBS_CHECK_IFELSE($2, $1="$$1 $2")
   ])

# Flag to select newest language standard supported
# Macros work such that first option that passes is the one we take
# gnu++17 code is clean, but SystemC in 2018 doesn't link with it (bug1339)
# gnu++14 is the newest that Verilator supports
# std++03 is the oldest that Verilator supports
#_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=gnu++17)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=gnu++14)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=gnu++11)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=gnu++03)
#_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=c++17)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=c++14)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=c++11)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=c++03)
AC_SUBST(CFG_CXXFLAGS_STD_NEWEST)
# And likewise oldest standard (same list above, backwards)
# This is used for internal testing
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=c++03)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=c++11)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=c++14)
#_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=std++17)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=gnu++03)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=gnu++11)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=gnu++14)
#_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_OLDEST,-std=gnu++17)
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
# For some reason -faligned-new does not work under Travis w/ clang but the
# configure test doesn't catch this either
AS_IF([test "x$TRAVIS_COMPILER" != xclang], [_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-faligned-new)])
CFG_CXX_FLAGS_CMAKE="-faligned-new"
m4_foreach([cflag],[
        [-fbracket-depth=4096],
        [-fcf-protection=none],
        [-mno-cet],
        [-Qunused-arguments],
        [-Wno-bool-operation],
        [-Wno-parentheses-equality],
        [-Wno-sign-compare],
        [-Wno-uninitialized],
        [-Wno-unused-but-set-variable],
        [-Wno-unused-parameter],
        [-Wno-unused-variable],
        [-Wno-shadow]],[
    _MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,cflag)
    # CMake will test what flags work itself, so pass all flags through to it
    CFG_CXX_FLAGS_CMAKE="$CFG_CXX_FLAGS_CMAKE cflag"
    ])
AC_SUBST(CFG_CXXFLAGS_NO_UNUSED)
AC_SUBST(CFG_CXX_FLAGS_CMAKE)

# Find multithread linker flags
m4_foreach([ldflag], [
        [-mt],
        [-pthread],
        [-lpthread],
        [-latomic]],[
    _MY_LDLIBS_CHECK_OPT(CFG_LDLIBS_THREADS,ldflag)
    # CMake will test what flags work itself, so pass all flags through to it
    CFG_LDFLAGS_THREADS_CMAKE="$CFG_LDFLAGS_THREADS_CMAKE ldflag"
    ])
AC_SUBST(CFG_LDLIBS_THREADS)
AC_SUBST(CFG_LDFLAGS_THREADS_CMAKE)

# When linking partially statically
if test "$CFG_ENABLE_PARTIAL_STATIC" = "yes"; then
  _MY_LDLIBS_CHECK_OPT(CFG_LDFLAGS_SRC, -static-libgcc)
  _MY_LDLIBS_CHECK_OPT(CFG_LDFLAGS_SRC, -static-libstdc++)
  _MY_LDLIBS_CHECK_OPT(CFG_LDFLAGS_SRC, -Xlinker -gc-sections)
  LTCMALLOC=-l:libtcmalloc_minimal.a
else
  LTCMALLOC=-ltcmalloc_minimal
fi
AC_SUBST(CFG_LDFLAGS_SRC)

# The pthread library is required by tcmalloc, so add it if it exists. If it
# does not, the tcmalloc check below will fail anyway, and linking against
# pthreads is harmless otherwise.
_MY_LDLIBS_CHECK_OPT(CFG_LIBS, -lpthread)

# Check if tcmalloc is available based on --enable-tcmalloc
_MY_LDLIBS_CHECK_IFELSE(
  $LTCMALLOC,
  [if test "$CFG_WITH_TCMALLOC" != "no"; then
    CFG_LIBS="$LTCMALLOC $CFG_LIBS";
    # If using tcmalloc, add some extra options to make the compiler not assume
    # it is using it's own versions of the standard library functions
    _MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-fno-builtin-malloc)
    _MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-fno-builtin-calloc)
    _MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-fno-builtin-realloc)
    _MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-fno-builtin-free)
   fi],
  [if test "$CFG_WITH_TCMALLOC" = "yes"; then
    AC_MSG_ERROR([--enable-tcmalloc was given but test for ${LTCMALLOC} failed])
   fi])
AC_SUBST(CFG_LIBS)

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

# Check compiler flag
if test "$CFG_WITH_THREADED" = "no" ; then
   if test "$CFG_WITH_PREC11" = "no" ; then
      AC_MSG_NOTICE([[]])
      AC_MSG_ERROR([[the $CXX compiler appears to not support C++11.

Verilator plans to require a C++11 or newer compiler in a future release,
unless sufficient people report problems. Therefore, if you do not have a
C++11 compiler, please post a message to
https://www.veripool.org/boards/3/topics/2580-Verilator-Requiring-C-11-compiler
indicating your OS and when you think C++11 might be ok, and then rerun
configure with the --enable-prec11 argument. Thanks.]])

   fi
fi

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
