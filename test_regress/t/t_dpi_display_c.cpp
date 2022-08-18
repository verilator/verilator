// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2011 by Wilson Snyder. This program is free software; you can
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
# include "Vt_dpi_display__Dpi.h"
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(CADENCE)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif
// clang-format on

#ifdef NEED_EXTERNS
extern "C" {

extern void dpii_display_call(const char* c);
}
#endif

// clang-format off
#ifndef VL_PRINTF
# define VL_PRINTF printf
#endif
// clang-format on

//======================================================================

void dpii_display_call(const char* c) { VL_PRINTF("dpii_display_call: '%s'\n", c); }
