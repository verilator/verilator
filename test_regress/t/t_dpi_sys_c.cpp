// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2009 by Wilson Snyder. This program is free software; you can
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
# include "Vt_dpi_sys__Dpi.h"
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(CADENCE)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif

#ifdef NEED_EXTERNS
extern "C" {

    extern void dpii_sys_task(int i);
    extern int dpii_sys_func(int i);

}
#endif

//======================================================================

static int hidden = 0;

void dpii_sys_task(int i) { hidden = i; }
int dpii_sys_func(int i) { return i + hidden; }
