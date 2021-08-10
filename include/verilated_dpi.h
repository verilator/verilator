// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilated DPI header
///
/// This file is included automatically by Verilator at the top of all C++
/// files it generates where DPI is used.  It contains DPI interface
/// functions required by the Verilated code.
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use.
///
//*************************************************************************

#ifndef VERILATOR_VERILATED_DPI_H_
#define VERILATOR_VERILATED_DPI_H_

#include "verilatedos.h"
#include "verilated.h"  // Also presumably included by caller
#include "verilated_heavy.h"  // Also presumably included by caller
#include "verilated_sym_props.h"

#include "svdpi.h"

//===================================================================
// SETTING OPERATORS

// Convert svBitVecVal to Verilator internal data
static inline void VL_SET_W_SVBV(int obits, WDataOutP owp, const svBitVecVal* lwp) VL_MT_SAFE {
    int words = VL_WORDS_I(obits);
    for (int i = 0; i < words - 1; ++i) owp[i] = lwp[i];
    owp[words - 1] = lwp[words - 1] & VL_MASK_I(obits);
}
static inline QData VL_SET_Q_SVBV(const svBitVecVal* lwp) VL_MT_SAFE {
    return VL_SET_QII(lwp[1], lwp[0]);
}
static inline IData VL_SET_I_SVBV(const svBitVecVal* lwp) VL_MT_SAFE { return lwp[0]; }

// Convert Verilator internal data to svBitVecVal
static inline void VL_SET_SVBV_W(int obits, svBitVecVal* owp, WDataInP lwp) VL_MT_SAFE {
    int words = VL_WORDS_I(obits);
    for (int i = 0; i < words - 1; ++i) owp[i] = lwp[i];
    owp[words - 1] = lwp[words - 1] & VL_MASK_I(obits);
}
static inline void VL_SET_SVBV_I(int, svBitVecVal* owp, IData ld) VL_MT_SAFE { owp[0] = ld; }
static inline void VL_SET_SVBV_Q(int, svBitVecVal* owp, QData ld) VL_MT_SAFE {
    VL_SET_WQ(owp, ld);
}

// Convert svLogicVecVal to Verilator internal data
// Note these functions ignore X/Z in svLogicVecVal
static inline void VL_SET_W_SVLV(int obits, WDataOutP owp, const svLogicVecVal* lwp) VL_MT_SAFE {
    int words = VL_WORDS_I(obits);
    for (int i = 0; i < words - 1; ++i) owp[i] = lwp[i].aval;
    owp[words - 1] = lwp[words - 1].aval & VL_MASK_I(obits);
}
static inline QData VL_SET_Q_SVLV(const svLogicVecVal* lwp) VL_MT_SAFE {
    return VL_SET_QII(lwp[1].aval, lwp[0].aval);
}
static inline IData VL_SET_I_SVLV(const svLogicVecVal* lwp) VL_MT_SAFE { return lwp[0].aval; }

// Convert Verilator internal data to svLogicVecVal
// Note these functions never create X/Z in svLogicVecVal
static inline void VL_SET_SVLV_W(int obits, svLogicVecVal* owp, WDataInP lwp) VL_MT_SAFE {
    int words = VL_WORDS_I(obits);
    for (int i = 0; i < words; ++i) owp[i].bval = 0;
    for (int i = 0; i < words - 1; ++i) owp[i].aval = lwp[i];
    owp[words - 1].aval = lwp[words - 1] & VL_MASK_I(obits);
}
static inline void VL_SET_SVLV_I(int, svLogicVecVal* owp, IData ld) VL_MT_SAFE {
    owp[0].aval = ld;
    owp[0].bval = 0;
}
static inline void VL_SET_SVLV_Q(int, svLogicVecVal* owp, QData ld) VL_MT_SAFE {
    VlWide<2> lwp;
    VL_SET_WQ(lwp, ld);
    owp[0].aval = lwp[0];
    owp[0].bval = 0;
    owp[1].aval = lwp[1];
    owp[1].bval = 0;
}

//======================================================================

#endif  // Guard
