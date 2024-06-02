// -*- mode: C++; c-file-style: "cc-mode" -*-

// DESCRIPTION: Verilator: Configure source; system configuration
//
// This file is part of Verilator.
//
// Code available from: https://verilator.org
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software;
// you can redistribute it and/or modify it under the terms of either
// the GNU Lesser General Public License Version 3 or
// the Perl Artistic License Version 2.0.
//
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


// Autoconf substitutes this with the strings from AC_INIT.
#define PACKAGE_STRING ""
#define PACKAGE_VERSION_NUMBER_STRING "0.000"
// Otherwise Autoheader generates it (with all the same macros and more)

// Force ccache recompilation on PACKAGE_STRING change
#ifndef VL_CPPCHECK
#ifndef PACKAGE_VERSION_STRING_CHAR
#define PACKAGE_VERSION_STRING_CHAR
PACKAGE_VERSION_STRING_CHAR
#endif
#endif

//**********************************************************************
//**** Configure-discovered library options

// Define if struct stat has st_mtim.tv_nsec (from configure)
#undef HAVE_STAT_NSEC

// Define if SystemC found
// - If defined, the default search path has it, so support is always enabled.
// - If undef, not system-wide, user can set SYSTEMC_INCLUDE.
#undef HAVE_SYSTEMC

// Define if coroutines are supported on this platform
#undef HAVE_COROUTINES

//**********************************************************************
//**** This file sometimes gets truncated, so check in consumers
#define HAVE_CONFIG_PACKAGE
