// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder. This program is free software; you can
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
///
/// \file
/// \brief Verilator: Common include for all Verilated C files that use DPI
///
///	This file is included automatically by Verilator at the top of
///	all C++ files it generates where DPI is used.  It contains
///	DPI interface functions required by the Verilated code.
///
/// Code available from: http://www.veripool.org/verilator
///
//*************************************************************************


#ifndef _VERILATED_DPI_H_
#define _VERILATED_DPI_H_ 1 ///< Header Guard

#include "verilated.h"   // Presumed done by caller
#include "svdpi.h"

//===================================================================
// SETTING OPERATORS

/// Return svBitVecVal from WData
static inline void VL_SET_W_SVBV(int obits, WDataOutP owp, svBitVecVal* lwp) {
    int words = VL_WORDS_I(obits);
    for (int i=0; i<words-1; i++) owp[i]=lwp[i];
    owp[words-1] = lwp[words-1] & VL_MASK_I(obits);
}
static inline void VL_SET_SVBV_W(int obits, svBitVecVal* owp, WDataInP lwp) {
    int words = VL_WORDS_I(obits);
    for (int i=0; i<words-1; i++) owp[i]=lwp[i];
    owp[words-1] = lwp[words-1] & VL_MASK_I(obits);
}
static inline void VL_SET_W_SVLV(int obits, WDataOutP owp, svLogicVecVal* lwp) {
    // Note we ignore X/Z in svLogicVecVal
    int words = VL_WORDS_I(obits);
    for (int i=0; i<words-1; i++) owp[i]=lwp[i].aval;
    owp[words-1] = lwp[words-1].aval & VL_MASK_I(obits);
}
static inline void VL_SET_SVLV_W(int obits, svLogicVecVal* owp, WDataInP lwp) {
    // Note we don't create X/Z in svLogicVecVal
    int words = VL_WORDS_I(obits);
    for (int i=0; i<words; i++) owp[i].bval=0;
    for (int i=0; i<words-1; i++) owp[i].aval=lwp[i];
    owp[words-1].aval = lwp[words-1] & VL_MASK_I(obits);
}

//======================================================================

#endif // _VERILATED_DPI_H_
