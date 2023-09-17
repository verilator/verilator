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

#include "svdpi.h"

#include <cstdio>
#include <cstring>

//======================================================================

// clang-format off
#if defined(VERILATOR)
# ifdef T_FUNC_WIDE_OUT
#  include "Vt_func_wide_out__Dpi.h"
# elif defined(T_FUNC_WIDE_OUT_NOINL)
#  include "Vt_func_wide_out_noinl__Dpi.h"
# else
#  error "Unknown test"
# endif
#elif defined(VCS)
# include "../vc_hdrs.h"
#else
# error "Unknown simulator for DPI test"
#endif
// clang-format on

//======================================================================

void dpii_inv_s12(const svBitVecVal* in, svBitVecVal* out) { out[0] = ~in[0]; }
void dpii_inv_u12(const svBitVecVal* in, svBitVecVal* out) { out[0] = ~in[0]; }
void dpii_inv_s70(const svBitVecVal* in, svBitVecVal* out) {
    out[0] = ~in[0];
    out[1] = ~in[1] & 0xf;
}
void dpii_inv_u70(const svBitVecVal* in, svBitVecVal* out) {
    out[0] = ~in[0];
    out[1] = ~in[1] & 0xf;
}
