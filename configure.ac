# DESCRIPTION: Process this file with autoconf to produce a configure script.
#
# Copyright 2003-2022 by Wilson Snyder. Verilator is free software; you
# can redistribute it and/or modify it under the terms of either the GNU Lesser
# General Public License Version 3 or the Perl Artistic License Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

# When releasing, also update header of Changes file
# and commit using "devel release" or "Version bump" message
# Then 'make maintainer-dist'
#AC_INIT([Verilator],[#.### YYYY-MM-DD])
#AC_INIT([Verilator],[#.### devel])
AC_INIT([Verilator],[4.227 devel],
        [https://verilator.org],
        [verilator],[https://verilator.org])

AC_CONFIG_HEADERS(src/config_build.h)
AC_CONFIG_FILES(Makefile src/Makefile src/Makefile_obj include/verilated.mk include/verilated_config.h verilator.pc verilator-config.cmake verilator-config-version.cmake)

# Version
AC_MSG_RESULT([configuring for $PACKAGE_STRING])
PACKAGE_VERSION_NUMBER=`AS_ECHO("$PACKAGE_VERSION") | sed 's/ .*//g'`
AC_SUBST(PACKAGE_VERSION_NUMBER)
AC_DEFINE_UNQUOTED([PACKAGE_VERSION_NUMBER_STRING],["$PACKAGE_VERSION_NUMBER"],[Package version as a number])
VERILATOR_VERSION_INTEGER=`AS_ECHO("$PACKAGE_VERSION") | [sed 's/\([0-9]\)\.\([0-9][0-9][0-9]\) .*/\1\2000/g']`
AC_SUBST(VERILATOR_VERSION_INTEGER)

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
                              [By default, for Verilation performance, Verilator
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
                               management in Verilator binary @<:@default=check@:>@])],
              [case "${enableval}" in
                yes) CFG_WITH_TCMALLOC=yes ;;
                no)  CFG_WITH_TCMALLOC=no ;;
                *)   AC_MSG_ERROR([bad value '${enableval}' for --enable-tcmalloc]) ;;
               esac],
              [CFG_WITH_TCMALLOC=check;])
AC_MSG_RESULT($CFG_WITH_TCMALLOC)

# Flag to enable -m32 build
AC_MSG_CHECKING(whether to use -m32)
AC_ARG_ENABLE([m32],
              [AS_HELP_STRING([--enable-m32],
                              [Use -m32 for all compilation and link,
                               including Verialtor and generated models.])],
              [case "${enableval}" in
                yes) CFG_ENABLE_M32=yes ;;
                no)  CFG_ENABLE_M32=no ;;
                *)   AC_MSG_ERROR([bad value '${enableval}' for --enable-m32]) ;;
               esac],
               CFG_ENABLE_M32=no)
AC_MSG_RESULT($CFG_ENABLE_M32)

# Flag to enable coverage build
AC_MSG_CHECKING(whether to build for coverage collection)
AC_ARG_ENABLE([coverage],
              [AS_HELP_STRING([--enable-coverage],
                              [Build Verilator for code coverage collection.
                               For developers only.])],
              [case "${enableval}" in
                yes) CFG_ENABLE_COVERAGE=yes ;;
                no)  CFG_ENABLE_COVERAGE=no ;;
                *)   AC_MSG_ERROR([bad value '${enableval}' for --enable-coverage]) ;;
               esac],
               CFG_ENABLE_COVERAGE=no)
AC_MSG_RESULT($CFG_ENABLE_COVERAGE)

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

# Compiler flags (ensure they are not empty to avoid configure defaults)
CFLAGS="$CFLAGS "
CPPFLAGS="$CPPFLAGS "
CXXFLAGS="$CXXFLAGS "
LDFLAGS="$LDFLAGS "

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

AC_CHECK_PROG(AR,ar,ar)
if test "x$AR" = "x" ; then
   AC_MSG_ERROR([Cannot find "ar" in your PATH, please install it])
fi

AC_PATH_PROG(PERL,perl)
if test "x$PERL" = "x" ; then
   AC_MSG_ERROR([Cannot find "perl" in your PATH, please install it])
fi

AC_PATH_PROG(PYTHON3,python3)
if test "x$PYTHON3" = "x" ; then
   AC_MSG_ERROR([Cannot find "python3" in your PATH, please install it])
fi

AC_PATH_PROG(LEX,flex)
if test "x$LEX" = "x" ; then
   AC_MSG_ERROR([Cannot find "flex" in your PATH, please install it])
fi
flex_version=$($LEX --version | head -1)
AC_MSG_RESULT([$LEX --version = $flex_version])

AC_PATH_PROG(YACC,bison)
if test "x$YACC" = "x" ; then
   AC_MSG_ERROR([Cannot find "bison" in your PATH, please install it])
fi
bison_version=$($YACC --version | head -1)
AC_MSG_RESULT([$YACC --version = $bison_version])

AC_CHECK_PROG(OBJCACHE,ccache,ccache)
if test "x$OBJCACHE" != "x" ; then
  objcache_version=$($OBJCACHE --version | head -1)
  AC_MSG_RESULT([objcache is $OBJCACHE --version = $objcache_version])
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

AC_DEFUN([_MY_CXX_CHECK_IFELSE],
   [# _MY_CXX_CHECK_IFELSE(option,action-if-supported,action-if-not-supported)
    # Check if compiler supports specific option. If it does,
    # do action-if-supported, otherwise do action-if-not-supported
    _MY_CXX_CHECK_FLAG($1)
    if test "$_my_result" = "yes" ; then
      true
      $2
    else
      true
      $3
    fi
   ])

AC_DEFUN([_MY_CXX_CHECK_SET],
   [# _MY_CXX_CHECK_SET(variable,option)
    # Check if compiler supports specific option. If it does,
    # set variable to option, only if not previously set.
    if test "$$1" = ""; then
       _MY_CXX_CHECK_IFELSE($2, $1="$2")
    fi
   ])

AC_DEFUN([_MY_CXX_CHECK_OPT],
   [# _MY_CXX_CHECK_OPT(variable,option)
    # Check if compiler supports specific option. If it does,
    # append option to variable
    _MY_CXX_CHECK_IFELSE($2, $1="$$1 $2")
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

# When using -m32. Check this first as later checks may fail with the -m32 flag.
if test "$CFG_ENABLE_M32" = "yes"; then
  _MY_CXX_CHECK_IFELSE(
    -m32,
    [CXX="$CXX -m32"],
    [AC_MSG_ERROR([--enable-m32 was given but compiler does not support -m32])])
fi

# Similarly, add the coverage flags early as they influence later checks.
if test "$CFG_ENABLE_COVERAGE" = "yes"; then
  _MY_CXX_CHECK_OPT(CXX,--coverage)
  # Otherwise inline may not show as uncovered
  #  If we use this then e.g. verilated.h functions properly show up
  #  if unused.
  #  However, VerilatedSerialize::write then changes from covered
  #  to uncovered (in G++ 9.3.0) even with all inlining turned off.
  #  Having false negative coverage is more effort then missing negatives.
  #  Also this seems to explode the runtime (since a lot more data).
  #  _MY_CXX_CHECK_OPT(CXX,-fkeep-inline-functions)
  # Otherwise static may not show as uncovered
  _MY_CXX_CHECK_OPT(CXX,-fkeep-static-functions)
  # Exceptions can pollute the branch coverage data
  _MY_CXX_CHECK_OPT(CXX,-fno-exceptions)
  # Define-out some impossible stuff
  _MY_CXX_CHECK_OPT(CXX,-DVL_GCOV)
fi

# Compiler flags to enable profiling
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_PROFILE,-pg)
AC_SUBST(CFG_CXXFLAGS_PROFILE)

# Flag to select newest language standard supported
# Macros work such that first option that passes is the one we take
# Currently enable c++17/c++14 due to packaged SystemC dependency
# c++17 is the newest that Verilator is regularly tested to support
# c++11 is the oldest that Verilator supports
# gnu is requried for Cygwin to compile verilated.h successfully
#_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=gnu++20)
#_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=c++20)
case "$(which lsb_release 2>&1 > /dev/null && lsb_release -d)" in
*Arch*Linux* | *Ubuntu*22.04*)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=gnu++17)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=c++17)
;;
esac
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=gnu++14)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=c++14)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=gnu++11)
_MY_CXX_CHECK_SET(CFG_CXXFLAGS_STD_NEWEST,-std=c++11)
AC_SUBST(CFG_CXXFLAGS_STD_NEWEST)

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
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-Wno-shadow)
AC_SUBST(CFG_CXXFLAGS_SRC)

# Flags for compiling Verilator parser always (in addition to above CFG_CXXFLAGS_SRC)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_PARSER,-Wno-char-subscripts)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_PARSER,-Wno-null-conversion)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_PARSER,-Wno-parentheses-equality)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_PARSER,-Wno-unused)
AC_SUBST(CFG_CXXFLAGS_PARSER)

# Flags for compiling the debug version of Verilator (in addition to above CFG_CXXFLAGS_SRC)
if test "$CFG_ENABLE_COVERAGE" = "no"; then # Do not optimize for the coverage build
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_DEBUG,-Og)
fi
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_DEBUG,-ggdb)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_DEBUG,-gz)
AC_SUBST(CFG_CXXFLAGS_DEBUG)

# Flags for linking the debug version of Verilator (in addition to above CFG_LDFLAGS_SRC)
_MY_LDLIBS_CHECK_OPT(CFG_LDFLAGS_DEBUG,-gz)
AC_SUBST(CFG_LDFLAGS_DEBUG)

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
        [-Wno-tautological-bitwise-compare],
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
CFG_LIBS="$LIBS $CFG_LIBS"
_MY_LDLIBS_CHECK_OPT(CFG_LIBS, -lpthread)

# Check libraries for MingW
_MY_LDLIBS_CHECK_OPT(CFG_LIBS, -lbcrypt)
_MY_LDLIBS_CHECK_OPT(CFG_LIBS, -lpsapi)

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

# Need C++11 at least
#Alternative: AX_CXX_COMPILE_STDCXX([11])
AC_DEFUN([_MY_CXX_CHECK_CXX_VER],
   [# _MY_CXX_CHECK_CXX_VER(flag) -- Check if compiler runs C++11
    # Set $_my_result
    AC_LINK_IFELSE(
     [AC_LANG_PROGRAM([#include <thread>
#if (__cplusplus < 201103L)
# error "Too old"
#endif
    ], [[ ]])],
     [_my_result=yes
      if test -s conftest.err; then
        if grep -e "$1" conftest.err >/dev/null; then
          _my_result=no
        fi
      fi],
     [_my_result=no])
   ])

AC_MSG_CHECKING(whether $CXX supports C++11)
_MY_CXX_CHECK_CXX_VER()
AC_MSG_RESULT($_my_result)
if test "$_my_result" = "no" ; then
   CXXFLAGS="$CXXFLAGS $CFG_CXXFLAGS_STD_NEWEST"
   CFG_CXX_FLAGS_CMAKE="$CFG_CXX_FLAGS_CMAKE $CFG_CXXFLAGS_STD_NEWEST"
   AC_MSG_CHECKING(whether $CXX supports C++11 with $CFG_CXXFLAGS_STD_NEWEST)
   _MY_CXX_CHECK_CXX_VER()
   AC_MSG_RESULT($_my_result)
fi
if test "$_my_result" = "no" ; then
   AC_MSG_NOTICE([[]])
   AC_MSG_ERROR([[the $CXX compiler appears to not support C++11.

Verilator requires a C++11 or newer compiler.]])

fi

# Checks for library functions.
AC_CHECK_MEMBER([struct stat.st_mtim.tv_nsec],
    [AC_DEFINE([HAVE_STAT_NSEC],[1],[Defined if struct stat has st_mtim.tv_nsec])],
    [], [#include <sys/stat.h>])

# HAVE_SYSTEMC
# - If found the default search path has it, so support is always enabled.
# - If not found or not system-wide, user can set SYSTEMC_INCLUDE.
# AC_CHECK_HEADERS seems to not locate on Travis-CI but include does work.
AC_MSG_CHECKING([whether SystemC is found (in system path)])
ACO_SAVE_LIBS="$LIBS"
LIBS="$LIBS -lsystemc"
AC_LINK_IFELSE(
    [AC_LANG_PROGRAM([[#include <systemc.h>
                     extern "C" int sc_main(int argc, char* argv[]) {}
                     ]],[[sc_version()]])],
    [_my_result=yes
     AC_DEFINE([HAVE_SYSTEMC],[1],[Defined if have SystemC library])],
    [_my_result=no])
AC_MSG_RESULT($_my_result)
LIBS="$ACO_SAVE_LIBS"
AC_SUBST(HAVE_SYSTEMC)

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
