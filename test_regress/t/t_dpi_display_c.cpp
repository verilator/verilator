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

#include <cstdio>
#include "svdpi.h"

//======================================================================

#if defined(VERILATOR)
# include "Vt_dpi_display__Dpi.h"
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(CADENCE)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif

#ifdef NEED_EXTERNS
extern "C" {

    extern void dpii_display_call(const char* c);
}
#endif

#ifndef VL_PRINTF
# define VL_PRINTF printf
#endif

//======================================================================

void dpii_display_call(const char* c) {
    VL_PRINTF("dpii_display_call: '%s'\n", c);
}
