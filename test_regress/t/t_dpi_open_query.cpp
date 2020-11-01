// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2020 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "svdpi.h"

// clang-format off
#if defined(VERILATOR)  // Verilator
# include "Vt_dpi_open_query__Dpi.h"
#elif defined(VCS)  // VCS
# include "../vc_hdrs.h"
#elif defined(NCSC)  // NC
# include "dpi-imp.h"
#elif defined(MS)  // ModelSim
# include "dpi.h"
#else
# error "Unknown simulator for DPI test"
#endif
// clang-format on

//======================================================================
// Implementations of imported functions
//======================================================================

// These are simple wrappers for the array querying functions themselves,
// see IEEE 1800-2017 H.12.2. Sadly on the SV side these have different
// signagures, and hence need to have different names here as well.

// 1 open dimension
int cSvLeft1(const svOpenArrayHandle h, int d) { return svLeft(h, d); }
int cSvRight1(const svOpenArrayHandle h, int d) { return svRight(h, d); }
int cSvLow1(const svOpenArrayHandle h, int d) { return svLow(h, d); }
int cSvHigh1(const svOpenArrayHandle h, int d) { return svHigh(h, d); }
int cSvIncrement1(const svOpenArrayHandle h, int d) { return svIncrement(h, d); }
int cSvSize1(const svOpenArrayHandle h, int d) { return svSize(h, d); }
int cSvDimensions1(const svOpenArrayHandle h) { return svDimensions(h); }

// 2 open dimensions
int cSvLeft2(const svOpenArrayHandle h, int d) { return svLeft(h, d); }
int cSvRight2(const svOpenArrayHandle h, int d) { return svRight(h, d); }
int cSvLow2(const svOpenArrayHandle h, int d) { return svLow(h, d); }
int cSvHigh2(const svOpenArrayHandle h, int d) { return svHigh(h, d); }
int cSvIncrement2(const svOpenArrayHandle h, int d) { return svIncrement(h, d); }
int cSvSize2(const svOpenArrayHandle h, int d) { return svSize(h, d); }
int cSvDimensions2(const svOpenArrayHandle h) { return svDimensions(h); }

// 3 open dimensions
int cSvLeft3(const svOpenArrayHandle h, int d) { return svLeft(h, d); }
int cSvRight3(const svOpenArrayHandle h, int d) { return svRight(h, d); }
int cSvLow3(const svOpenArrayHandle h, int d) { return svLow(h, d); }
int cSvHigh3(const svOpenArrayHandle h, int d) { return svHigh(h, d); }
int cSvIncrement3(const svOpenArrayHandle h, int d) { return svIncrement(h, d); }
int cSvSize3(const svOpenArrayHandle h, int d) { return svSize(h, d); }
int cSvDimensions3(const svOpenArrayHandle h) { return svDimensions(h); }

// 4 open dimensions
int cSvLeft4(const svOpenArrayHandle h, int d) { return svLeft(h, d); }
int cSvRight4(const svOpenArrayHandle h, int d) { return svRight(h, d); }
int cSvLow4(const svOpenArrayHandle h, int d) { return svLow(h, d); }
int cSvHigh4(const svOpenArrayHandle h, int d) { return svHigh(h, d); }
int cSvIncrement4(const svOpenArrayHandle h, int d) { return svIncrement(h, d); }
int cSvSize4(const svOpenArrayHandle h, int d) { return svSize(h, d); }
int cSvDimensions4(const svOpenArrayHandle h) { return svDimensions(h); }
