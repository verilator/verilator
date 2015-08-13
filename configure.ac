# DESCRIPTION: Process this file with autoconf to produce a configure script.
#
# Copyright 2003-2015 by Wilson Snyder. Verilator is free software; you can
# redistribute it and/or modify it under the terms of either the GNU Lesser
# General Public License Version 3 or the Perl Artistic License Version 2.0.

#AC_INIT([Verilator],[#.### YYYY-MM-DD])
#AC_INIT([Verilator],[#.### devel])
AC_INIT([Verilator],[3.876 2015-08-12])
# When releasing, also update header of Changes file

AC_CONFIG_HEADER(src/config_build.h)
AC_CONFIG_FILES(Makefile src/Makefile src/Makefile_obj include/verilated.mk include/verilated_config.h verilator.pc)

AC_MSG_RESULT([configuring for $PACKAGE_STRING])

# Special Substitutions - CFG_WITH_DEFENV
AC_MSG_CHECKING(whether to disable hardcoded paths)
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

AC_DEFUN([_MY_CXX_CHECK_OPT],
   [# _MY_CXX_CHECK_OPT(flag) -- Check if compiler supports specific options
    ACO_SAVE_CXXFLAGS="$CXXFLAGS"
    # -Werror needed otherwise unknown -Wno-div-by-zero won't report problems
    CXXFLAGS="$CXXFLAGS $2 -Werror"
    AC_MSG_CHECKING([whether $CXX accepts $2])
    AC_COMPILE_IFELSE(
         [AC_LANG_PROGRAM([],[])],
	 [_my_result=yes
	  if test -s conftest.err; then
	    if grep -e "$2" conftest.err >/dev/null; then
	      _my_result=no
	    fi
	  fi],
	 [_my_result=no])
    AC_MSG_RESULT($_my_result)
    if test "$_my_result" = "yes" ; then
       $1="$$1 $2"
    fi
    CXXFLAGS="$ACO_SAVE_CXXFLAGS"
   ])# _MY_CXX_CHECK_OPT

# Flags for compiling Verilator internals including parser
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-Wno-unused-parameter)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-Wno-char-subscripts)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_SRC,-Qunused-arguments)
AC_SUBST(CFG_CXXFLAGS_SRC)

# Flags for compiling Verilator parser
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_PARSER,-Wno-unused)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_PARSER,-Wno-parentheses-equality)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_PARSER,-Wno-null-conversion)
AC_SUBST(CFG_CXXFLAGS_PARSER)

# Flags for Verilated makefile
# For example, -Wno-div-by-zero isn't in 4.1.2
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-char-subscripts)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-parentheses-equality)
# Random code often does / 0.  Unfortunately VL_DIV_I(0,0) will warn
# without this flag, even though there's a conditional to prevent the divide.
# We still don't add no-div-by-zero as it throws message to stdout, though doesn't die.
#_MY_CXX_CHECK_OPT(-Wno-div-by-zero)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-sign-compare)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-uninitialized)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-unused-but-set-variable)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-unused-parameter)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Wno-unused-variable)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-fbracket-depth=4096)
_MY_CXX_CHECK_OPT(CFG_CXXFLAGS_NO_UNUSED,-Qunused-arguments)
AC_SUBST(CFG_CXXFLAGS_NO_UNUSED)

# Checks for library functions.

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
