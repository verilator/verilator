// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2020 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "svdpi.h"

#include <cstdio>
#include <cstring>
#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

//======================================================================

// clang-format off
#if defined(VERILATOR)
# include "Vt_dpi_open_oob_bad__Dpi.h"
#else
# error "Unknown simulator for DPI test"
#endif
// clang-format on

//======================================================================

int errors = 0;

void dpii_nullptr() {
    printf("%s:\n", __func__);
    // These cause fatal errors, so each would need a separate run
    // svOpenArrayHandle h = nullptr;
    // svBitVecVal bit_vec_val[2];
    // svLogicVecVal logic_vec_val[2];
    // svDimensions(h);
    // svGetArrayPtr(h);
    // svHigh(h, 0);
    // svIncrement(h, 0);
    // svLeft(h, 0);
    // svLow(h, 0);
    // svRight(h, 0);
    // svSize(h, 0);
    // svSizeOfArray(h);
    //
    // svGetArrElemPtr(h, 0);
    // svGetArrElemPtr1(h, 0);
    // svGetArrElemPtr2(h, 0, 0);
    // svGetArrElemPtr3(h, 0, 0, 0);
    // svGetBitArrElem(h, 0);
    // svGetBitArrElem1(h, 0);
    // svGetBitArrElem1VecVal(bit_vec_val, h, 0);
    // svGetBitArrElem2(h, 0, 0);
    // svGetBitArrElem2VecVal(bit_vec_val, h, 0, 0);
    // svGetBitArrElem3(h, 0, 0, 0);
    // svGetBitArrElem3VecVal(bit_vec_val, h, 0, 0, 0);
    // svGetBitArrElemVecVal(bit_vec_val, h, 0);
    // svGetLogicArrElem(h, 0);
    // svGetLogicArrElem1(h, 0);
    // svGetLogicArrElem1VecVal(logic_vec_val, h, 0);
    // svGetLogicArrElem2(h, 0, 0);
    // svGetLogicArrElem2VecVal(logic_vec_val, h, 0, 0);
    // svGetLogicArrElem3(h, 0, 0, 0);
    // svGetLogicArrElem3VecVal(logic_vec_val, h, 0, 0, 0);
    // svGetLogicArrElemVecVal(logic_vec_val, h, 0);
    // svPutBitArrElem(h, 0, 0);
    // svPutBitArrElem1(h, 0, 0);
    // svPutBitArrElem1VecVal(h, bit_vec_val, 0);
    // svPutBitArrElem2(h, 0, 0, 0);
    // svPutBitArrElem2VecVal(h, bit_vec_val, 0, 0);
    // svPutBitArrElem3(h, 0, 0, 0, 0);
    // svPutBitArrElem3VecVal(h, bit_vec_val, 0, 0, 0);
    // svPutBitArrElemVecVal(h, bit_vec_val, 0);
    // svPutLogicArrElem(h, 0, 0);
    // svPutLogicArrElem1(h, 0, 0);
    // svPutLogicArrElem1VecVal(h, logic_vec_val, 0);
    // svPutLogicArrElem2(h, 0, 0, 0);
    // svPutLogicArrElem2VecVal(h, logic_vec_val, 0, 0);
    // svPutLogicArrElem3(h, 0, 0, 0, 0);
    // svPutLogicArrElem3VecVal(h, logic_vec_val, 0, 0, 0);
    // svPutLogicArrElemVecVal(h, logic_vec_val, 0);
}

void dpii_int_u3(const svOpenArrayHandle i) {
    printf("%s:\n", __func__);
    // Correct usage
    intptr_t ip = (intptr_t)svGetArrElemPtr3(i, 1, 2, 3);
    TEST_CHECK_HEX_NE(ip, 0);
    // Out of bounds
    ip = (intptr_t)svGetArrElemPtr3(i, 1, 2, 30);
    TEST_CHECK_HEX_EQ(ip, 0);
    ip = (intptr_t)svGetArrElemPtr3(i, 1, 20, 3);
    TEST_CHECK_HEX_EQ(ip, 0);
    ip = (intptr_t)svGetArrElemPtr3(i, 10, 2, 3);
    TEST_CHECK_HEX_EQ(ip, 0);
    ip = (intptr_t)svGetArrElemPtr1(i, 30);
    TEST_CHECK_HEX_EQ(ip, 0);
}

void dpii_real_u1(const svOpenArrayHandle i) {
    printf("%s:\n", __func__);
    svBitVecVal bit_vec_val[4];
    svLogicVecVal logic_vec_val[4];

    svGetBitArrElem(i, 0);
    svGetBitArrElem1(i, 0);
    svGetBitArrElem1VecVal(bit_vec_val, i, 0);
    svGetBitArrElemVecVal(bit_vec_val, i, 0);
    svGetLogicArrElem(i, 0);
    svGetLogicArrElem1(i, 0);
    svGetLogicArrElem1VecVal(logic_vec_val, i, 0);
    svGetLogicArrElemVecVal(logic_vec_val, i, 0);
    svPutBitArrElem(i, 0, 0);
    svPutBitArrElem1(i, 0, 0);
    svPutBitArrElem1VecVal(i, bit_vec_val, 0);
    svPutBitArrElemVecVal(i, bit_vec_val, 0);
    svPutLogicArrElem(i, 0, 0);
    svPutLogicArrElem1(i, 0, 0);
    svPutLogicArrElem1VecVal(i, logic_vec_val, 0);
    svPutLogicArrElemVecVal(i, logic_vec_val, 0);
}

void dpii_bit_u6(const svOpenArrayHandle i) {
    printf("%s:\n", __func__);
    svBitVecVal bit_vec_val[4];
    svLogicVecVal logic_vec_val[4];

    svGetBitArrElem(i, 0, 0, 0, 0, 0, 0);
    svGetBitArrElemVecVal(bit_vec_val, i, 0, 0, 0, 0, 0, 0);
    svGetLogicArrElem(i, 0, 0, 0, 0, 0, 0);
    svGetLogicArrElemVecVal(logic_vec_val, i, 0, 0, 0, 0, 0, 0);
    svPutBitArrElem(i, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    svPutBitArrElemVecVal(i, bit_vec_val, 0, 0, 0, 0, 0, 0);
    svPutLogicArrElem(i, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
    svPutLogicArrElemVecVal(i, logic_vec_val, 0, 0, 0, 0, 0, 0);
}

void dpii_real_u6(const svOpenArrayHandle i) {
    printf("%s:\n", __func__);
    svGetArrElemPtr(i, 0, 0, 0, 0, 0, 0);
}
