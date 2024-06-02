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
# include "Vt_dpi_open_vecval__Dpi.h"
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(NC)
# define NEED_EXTERNS
// #elif defined(MS)
// # define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif
// clang-format on

#ifdef NEED_EXTERNS
extern "C" {
// If get ncsim: *F,NOFDPI: Function {foo} not found in default libdpi.
// Then probably forgot to list a function here.

extern int dpii_failure();
}
#endif

int errors = 0;
int dpii_failure() { return errors; }

static void _invert(int bits, svBitVecVal o[], const svBitVecVal i[]) {
    for (int w = 0; w < SV_PACKED_DATA_NELEMS(bits); ++w) o[w] = ~i[w];
    o[SV_PACKED_DATA_NELEMS(bits) - 1] &= SV_MASK(bits & 31);
}
static void _invert(int bits, svLogicVecVal o[], const svLogicVecVal i[]) {
    for (int w = 0; w < SV_PACKED_DATA_NELEMS(bits); ++w) {
        o[w].aval = ~i[w].aval;
        o[w].bval = 0;
    }
    o[SV_PACKED_DATA_NELEMS(bits) - 1].aval &= SV_MASK(bits & 31);
    o[SV_PACKED_DATA_NELEMS(bits) - 1].bval &= SV_MASK(bits & 31);
}

static bool _same(int bits, const svBitVecVal o[], const svBitVecVal i[]) {
    for (int w = 0; w < SV_PACKED_DATA_NELEMS(bits); ++w) {
        svBitVecVal mask = 0xffffffff;
        if (w == SV_PACKED_DATA_NELEMS(bits) - 1) mask = SV_MASK(bits & 31);
        if ((o[w] & mask) != (i[w] & mask)) return false;
    }
    return true;
}
static bool _same(int bits, const svLogicVecVal o[], const svLogicVecVal i[]) {
    for (int w = 0; w < SV_PACKED_DATA_NELEMS(bits); ++w) {
        svBitVecVal mask = 0xffffffff;
        if (w == SV_PACKED_DATA_NELEMS(bits) - 1) mask = SV_MASK(bits & 31);
        if ((o[w].aval & mask) != (i[w].aval & mask)) return false;
        if ((o[w].bval & mask) != (i[w].bval & mask)) return false;
    }
    return true;
}

void dpii_unused(const svOpenArrayHandle u) {}

//======================================================================

static void _dpii_bit_vecval_ux(int bits, int p, int u, const svOpenArrayHandle i,
                                const svOpenArrayHandle o, const svOpenArrayHandle q) {
    printf("%s: bits=%d p=%d u=%d\n", __func__, bits, p, u);

    int dim = svDimensions(i);
#ifndef NC
    // NC always returns zero and warns
    TEST_CHECK_HEX_EQ(dim, u);
#endif

    svBitVecVal vv[SV_PACKED_DATA_NELEMS(bits)];
    svBitVecVal vv2[SV_PACKED_DATA_NELEMS(bits)];
    svBitVecVal vo[SV_PACKED_DATA_NELEMS(bits)];
    for (int a = svLow(i, 1); a <= svHigh(i, 1); ++a) {
        fflush(stdout);
        if (dim == 1) {
            svGetBitArrElemVecVal(vv, i, a);
            svGetBitArrElem1VecVal(vv2, i, a);
            TEST_CHECK_HEX_EQ(_same(bits, vv, vv2), true);
            _invert(bits, vo, vv);
            svPutBitArrElemVecVal(o, vo, a);
            svPutBitArrElem1VecVal(q, vo, a);
        } else {
            for (int b = svLow(i, 2); b <= svHigh(i, 2); ++b) {
                if (dim == 2) {
                    svGetBitArrElemVecVal(vv, i, a, b);
                    svGetBitArrElem2VecVal(vv2, i, a, b);
                    TEST_CHECK_HEX_EQ(_same(bits, vv, vv2), true);
                    _invert(bits, vo, vv);
                    svPutBitArrElemVecVal(o, vo, a, b);
                    svPutBitArrElem2VecVal(q, vo, a, b);
                } else {
                    for (int c = svLow(i, 3); c <= svHigh(i, 3); ++c) {
                        if (dim == 3) {
                            svGetBitArrElemVecVal(vv, i, a, b, c);
                            svGetBitArrElem3VecVal(vv2, i, a, b, c);
                            TEST_CHECK_HEX_EQ(_same(bits, vv, vv2), true);
                            _invert(bits, vo, vv);
                            svPutBitArrElemVecVal(o, vo, a, b, c);
                            svPutBitArrElem3VecVal(q, vo, a, b, c);
                        }
                    }
                }
            }
        }
    }
    fflush(stdout);
}
void dpii_bit_vecval_p1_u1(int bits, int p, int u, const svOpenArrayHandle i,
                           const svOpenArrayHandle o, const svOpenArrayHandle q) {
    _dpii_bit_vecval_ux(bits, p, u, i, o, q);
}
void dpii_bit61_vecval_p1_u1(int bits, int p, int u, const svOpenArrayHandle i,
                             const svOpenArrayHandle o, const svOpenArrayHandle q) {
    _dpii_bit_vecval_ux(bits, p, u, i, o, q);
}
void dpii_bit92_vecval_p1_u1(int bits, int p, int u, const svOpenArrayHandle i,
                             const svOpenArrayHandle o, const svOpenArrayHandle q) {
    _dpii_bit_vecval_ux(bits, p, u, i, o, q);
}
void dpii_bit12_vecval_p1_u2(int bits, int p, int u, const svOpenArrayHandle i,
                             const svOpenArrayHandle o, const svOpenArrayHandle q) {
    _dpii_bit_vecval_ux(bits, p, u, i, o, q);
}
void dpii_bit29_vecval_p1_u3(int bits, int p, int u, const svOpenArrayHandle i,
                             const svOpenArrayHandle o, const svOpenArrayHandle q) {
    _dpii_bit_vecval_ux(bits, p, u, i, o, q);
}

//======================================================================

static void _dpii_logic_vecval_ux(int bits, int p, int u, const svOpenArrayHandle i,
                                  const svOpenArrayHandle o, const svOpenArrayHandle q) {
    printf("%s: bits=%d p=%d u=%d\n", __func__, bits, p, u);

    int dim = svDimensions(i);
#ifndef NC
    // NC always returns zero and warns
    TEST_CHECK_HEX_EQ(dim, u);
#endif

    svLogicVecVal vv[SV_PACKED_DATA_NELEMS(bits)];
    svLogicVecVal vv2[SV_PACKED_DATA_NELEMS(bits)];
    svLogicVecVal vo[SV_PACKED_DATA_NELEMS(bits)];
    for (int a = svLow(i, 1); a <= svHigh(i, 1); ++a) {
        fflush(stdout);
        if (dim == 1) {
            svGetLogicArrElemVecVal(vv, i, a);
            svGetLogicArrElem1VecVal(vv2, i, a);
            TEST_CHECK_HEX_EQ(_same(bits, vv, vv2), true);
            _invert(bits, vo, vv);
            svPutLogicArrElemVecVal(o, vo, a);
            svPutLogicArrElem1VecVal(q, vo, a);
        } else {
            for (int b = svLow(i, 2); b <= svHigh(i, 2); ++b) {
                if (dim == 2) {
                    svGetLogicArrElemVecVal(vv, i, a, b);
                    svGetLogicArrElem2VecVal(vv2, i, a, b);
                    TEST_CHECK_HEX_EQ(_same(bits, vv, vv2), true);
                    _invert(bits, vo, vv);
                    svPutLogicArrElemVecVal(o, vo, a, b);
                    svPutLogicArrElem2VecVal(q, vo, a, b);
                } else {
                    for (int c = svLow(i, 3); c <= svHigh(i, 3); ++c) {
                        if (dim == 3) {
                            svGetLogicArrElemVecVal(vv, i, a, b, c);
                            svGetLogicArrElem3VecVal(vv2, i, a, b, c);
                            TEST_CHECK_HEX_EQ(_same(bits, vv, vv2), true);
                            _invert(bits, vo, vv);
                            svPutLogicArrElemVecVal(o, vo, a, b, c);
                            svPutLogicArrElem3VecVal(q, vo, a, b, c);
                        }
                    }
                }
            }
        }
    }
    fflush(stdout);
}
void dpii_logic_vecval_p1_u1(int bits, int p, int u, const svOpenArrayHandle i,
                             const svOpenArrayHandle o, const svOpenArrayHandle q) {
    _dpii_logic_vecval_ux(bits, p, u, i, o, q);
}
void dpii_logic61_vecval_p1_u1(int bits, int p, int u, const svOpenArrayHandle i,
                               const svOpenArrayHandle o, const svOpenArrayHandle q) {
    _dpii_logic_vecval_ux(bits, p, u, i, o, q);
}
void dpii_logic92_vecval_p1_u1(int bits, int p, int u, const svOpenArrayHandle i,
                               const svOpenArrayHandle o, const svOpenArrayHandle q) {
    _dpii_logic_vecval_ux(bits, p, u, i, o, q);
}
void dpii_logic12_vecval_p1_u2(int bits, int p, int u, const svOpenArrayHandle i,
                               const svOpenArrayHandle o, const svOpenArrayHandle q) {
    _dpii_logic_vecval_ux(bits, p, u, i, o, q);
}
void dpii_logic29_vecval_p1_u3(int bits, int p, int u, const svOpenArrayHandle i,
                               const svOpenArrayHandle o, const svOpenArrayHandle q) {
    _dpii_logic_vecval_ux(bits, p, u, i, o, q);
}
