// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2011-2011 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include <cstdio>
#include <cstring>
#include "svdpi.h"

//======================================================================

#if defined(VERILATOR)
# include "Vt_dpi_shortcircuit__Dpi.h"
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(CADENCE)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif

#ifdef NEED_EXTERNS
extern "C" {
    extern int  dpii_clear ();
    extern int   dpii_count (int idx);
    extern unsigned char  dpii_inc0 (int idx);
    extern unsigned char  dpii_inc1 (int idx);
    extern unsigned char  dpii_incx (int idx, unsigned char value);
}
#endif

//======================================================================

#define COUNTERS 16
static int global_count[COUNTERS];

int dpii_clear () {
    for (int i=0; i<COUNTERS; ++i) global_count[i] = 0;
    return 0;
}
int dpii_count (int idx) {
    return (idx >= 0 && idx<COUNTERS) ? global_count[idx] : -1;
}
unsigned char dpii_incx (int idx, unsigned char value) {
    if (idx >= 0 && idx<COUNTERS) global_count[idx]++;
    return value;
}
unsigned char dpii_inc0 (int idx) { return dpii_incx(idx,false); }
unsigned char dpii_inc1 (int idx) { return dpii_incx(idx,true); }
