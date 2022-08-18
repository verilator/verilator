// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2010-2011 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "svdpi.h"

#include <cstdio>

//======================================================================

// clang-format off
#if defined(VERILATOR)
# include "Vt_flag_ldflags__Dpi.h"
#else
# error "Unknown simulator for DPI test"
#endif

//======================================================================

#ifndef CFLAGS_FROM_CMDLINE
# error "CFLAGS_FROM_CMDLINE not set - not passed down?"
#endif
#ifndef CFLAGS2_FROM_CMDLINE
# error "CFLAGS2_FROM_CMDLINE not set - not passed down?"
#endif
// clang-format on

void dpii_c_library() {}
