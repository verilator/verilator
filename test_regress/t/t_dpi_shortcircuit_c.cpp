// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2011-2011 Wilson Snyder
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
// clang-format on

#ifdef NEED_EXTERNS
extern "C" {
extern void dpii_clear();
extern int dpii_count(int idx);
extern unsigned char dpii_inc0(int idx);
extern unsigned char dpii_inc1(int idx);
extern unsigned char dpii_incx(int idx, unsigned char value);
}
#endif

//======================================================================

#define COUNTERS 16
static int global_count[COUNTERS];

void dpii_clear() {
    for (int i = 0; i < COUNTERS; ++i) global_count[i] = 0;
}
int dpii_count(int idx) { return (idx >= 0 && idx < COUNTERS) ? global_count[idx] : -1; }
unsigned char dpii_incx(int idx, unsigned char value) {
    if (idx >= 0 && idx < COUNTERS) ++global_count[idx];
    return value;
}
unsigned char dpii_inc0(int idx) { return dpii_incx(idx, 0); }
unsigned char dpii_inc1(int idx) { return dpii_incx(idx, 1); }
