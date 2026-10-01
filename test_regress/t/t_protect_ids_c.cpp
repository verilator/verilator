// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2009-2009 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "svdpi.h"

#include <cstdio>
#include <cstring>

//======================================================================

// clang-format off
#if defined(VERILATOR)
# include VM_PREFIX_INCLUDE_DPI
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(CADENCE)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif

#ifdef NEED_EXTERNS
# error "Not supported"
#endif
// clang-format on

//======================================================================

int dpii_a_func(int i) {
    int o = dpix_a_func(i);
    return o;
}

int dpii_a_task(int i, int* op) {
    (void)dpix_a_task(i, op);
    return 0;
}
