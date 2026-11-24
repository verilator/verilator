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

void i_bit_1_33(svBitVecVal* o, const svBitVecVal* in) {
    o[0] = in[0] + 1;
    o[1] = (in[1] + (o[0] == 0)) & 0x1;
}

void i_bit_t_33(svBitVecVal* o, const svBitVecVal* in) {
    o[0] = in[0] << 1;
    o[1] = ((in[1] << 1) | (in[0] >> 31)) & 0x1;
}

void i_struct_2_state_33(svBitVecVal* o, const svBitVecVal* in) {
    // Keep member y, clear member x
    o[0] = in[0] & 0x1ffff;
    o[1] = 0;
}

void i_logic2(svLogicVecVal* o, const svLogicVecVal* in) {
    o[0].aval = ((in[0].aval & 0x1) << 1) | ((in[0].aval >> 1) & 0x1);
    o[0].bval = ((in[0].bval & 0x1) << 1) | ((in[0].bval >> 1) & 0x1);
}

void i_logic100_xz(svLogicVecVal* o, const svLogicVecVal* in) {
    // X and Z read as their aval bit, and bits above the width are ignored
    for (int i = 0; i < 4; ++i) {
        o[i].aval = in[i].aval;
        o[i].bval = 0xffffffff;
    }
    o[3].aval |= 0xfffffff0;
}

void i_logic65_t(svLogicVecVal* o, const svLogicVecVal* in) {
    for (int i = 0; i < 3; ++i) {
        o[i].aval = ~in[i].aval;
        o[i].bval = 0;
    }
}

void i_integer(svLogicVecVal* o, int in) {
    o[0].aval = in * 2;
    o[0].bval = 0;
}

void i_union_4_state_17(svLogicVecVal* o, const svLogicVecVal* in) {
    o[0].aval = ((in[0].aval << 1) | (in[0].aval >> 16)) & 0x1ffff;
    o[0].bval = 0;
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
    const svBitVecVal b95in[3] = {0x89abcdef, 0x01234567, 0x76543210};
    svBitVecVal b95out[3] = {0, 0, 0};
    e_bit95_t(b95out, b95in);
    if (b95out[0] != ~b95in[0] || b95out[1] != ~b95in[1]
        || (b95out[2] & 0x7fffffff) != (~b95in[2] & 0x7fffffff)) {
        printf("%%Error: e_bit95_t got %08x_%08x_%08x\n", b95out[2], b95out[1], b95out[0]);
        ++errors;
    }
    const svBitVecVal uin[3] = {0xffffffff, 0xffffffff, 0x0};
    svBitVecVal uout[3] = {0, 0, 0};
    e_union_2_state_65(uout, uin);
    if (uout[0] != 0 || uout[1] != 0 || (uout[2] & 0x1) != 0x1) {
        printf("%%Error: e_union_2_state_65 got %08x_%08x_%08x\n", uout[2], uout[1], uout[0]);
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
    const svLogicVecVal l7in[1] = {{0x2a, 0}};
    svLogicVecVal l7out[1] = {{0, 0}};
    e_logic_8_2(l7out, l7in);
    if ((l7out[0].aval & 0x7f) != 0x55 || (l7out[0].bval & 0x7f) != 0) {
        printf("%%Error: e_logic_8_2 got %08x/%08x\n", l7out[0].aval, l7out[0].bval);
        ++errors;
    }
    svLogicVecVal iout[1] = {{0, 0}};
    e_integer(iout, 41);
    if (iout[0].aval != 42 || iout[0].bval != 0) {
        printf("%%Error: e_integer got %08x/%08x\n", iout[0].aval, iout[0].bval);
        ++errors;
    }
    // Members x = 0xa, y = 0x13
    const svLogicVecVal s9in[1] = {{0x153, 0}};
    svLogicVecVal s9out[1] = {{0, 0}};
    e_struct_4_state_9(s9out, s9in);
    if ((s9out[0].aval & 0x1ff) != 0x7a || (s9out[0].bval & 0x1ff) != 0) {
        printf("%%Error: e_struct_4_state_9 got %08x/%08x\n", s9out[0].aval, s9out[0].bval);
        ++errors;
    }
    return errors;
}
