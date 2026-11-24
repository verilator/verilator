// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "svdpi.h"

#include <cstdio>

#include VM_PREFIX_INCLUDE_DPI

void i_bit33(svBitVecVal* o, const svBitVecVal* in) {
    o[0] = ~in[0];
    o[1] = ~in[1] & 0x1;
}

void i_bit128(svBitVecVal* o, const svBitVecVal* in) {
    for (int i = 0; i < 4; ++i) o[i] = ~in[i];
}

void i_logic2(svLogicVecVal* o, const svLogicVecVal* in) {
    o[0].aval = ((in[0].aval & 0x1) << 1) | ((in[0].aval >> 1) & 0x1);
    o[0].bval = ((in[0].bval & 0x1) << 1) | ((in[0].bval >> 1) & 0x1);
}

void i_logic100(svLogicVecVal* o, const svLogicVecVal* in) {
    for (int i = 0; i < 4; ++i) o[i] = in[i];
}

int check_exports() {
    int errors = 0;
    const svBitVecVal bin[3] = {0x89abcdef, 0x01234567, 0x1};
    svBitVecVal bout[3] = {0, 0, 0};
    e_bit65(bout, bin);
    if (bout[0] != ~bin[0] || bout[1] != ~bin[1] || (bout[2] & 0x1) != 0) {
        printf("%%Error: e_bit65 got %08x_%08x_%08x\n", bout[2], bout[1], bout[0]);
        ++errors;
    }
    const svLogicVecVal lin[2] = {{0x89abcdef, 0}, {0x00123456, 0}};
    svLogicVecVal lout[2] = {{0, 0}, {0, 0}};
    e_logic56(lout, lin);
    if (lout[0].aval != lin[0].aval || lout[0].bval != 0
        || (lout[1].aval & 0xffffff) != lin[1].aval || (lout[1].bval & 0xffffff) != 0) {
        printf("%%Error: e_logic56 got %08x/%08x_%08x/%08x\n", lout[1].aval, lout[1].bval,
               lout[0].aval, lout[0].bval);
        ++errors;
    }
    return errors;
}
