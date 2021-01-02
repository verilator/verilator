// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2017 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include <cstdio>
#include <cstring>
#include <iostream>
#include "svdpi.h"

//======================================================================

// clang-format off
#if defined(VERILATOR)
# include "Vt_dpi_open_elem__Dpi.h"
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

void dpii_bit_elem_p0_u1(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                         const svOpenArrayHandle q);
void dpii_bit_elem_p0_u2(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                         const svOpenArrayHandle q);
void dpii_bit_elem_p0_u3(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                         const svOpenArrayHandle q);
void dpii_logic_elem_p0_u1(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                           const svOpenArrayHandle q);
void dpii_logic_elem_p0_u2(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                           const svOpenArrayHandle q);
void dpii_logic_elem_p0_u3(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                           const svOpenArrayHandle q);

extern int dpii_failure();
}
#endif

int failure = 0;
int dpii_failure() { return failure; }

#define CHECK_RESULT_HEX(got, exp) \
    do { \
        if ((got) != (exp)) { \
            std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << std::hex \
                      << ": GOT=" << (got) << "   EXP=" << (exp) << std::endl; \
            failure = __LINE__; \
        } \
    } while (0)

#define CHECK_RESULT_HEX_NE(got, exp) \
    do { \
        if ((got) == (exp)) { \
            std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << std::hex \
                      << ": GOT=" << (got) << "   EXP!=" << (exp) << std::endl; \
            failure = __LINE__; \
        } \
    } while (0)

void dpii_unused(const svOpenArrayHandle u) {}

//======================================================================

static void _dpii_bit_elem_ux(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                              const svOpenArrayHandle q) {
    int dim = svDimensions(i);
#ifndef NC
    // NC always returns zero and warns
    CHECK_RESULT_HEX(dim, u);
    // svSizeOfArray(i) undeterministic as not in C representation
#endif

    for (int a = svLow(i, 1); a <= svHigh(i, 1); ++a) {
        fflush(stdout);
        if (dim == 1) {
            svBit v = svGetBitArrElem(i, a);
            svBit v2 = svGetBitArrElem1(i, a);
            CHECK_RESULT_HEX(v, v2);
            svPutBitArrElem(o, v ? 0 : 1, a);
            svPutBitArrElem1(q, v ? 0 : 1, a);
        } else {
            for (int b = svLow(i, 2); b <= svHigh(i, 2); ++b) {
                if (dim == 2) {
                    svBit v = svGetBitArrElem(i, a, b);
                    svBit v2 = svGetBitArrElem2(i, a, b);
                    CHECK_RESULT_HEX(v, v2);
                    svPutBitArrElem(o, v ? 0 : 1, a, b);
                    svPutBitArrElem2(q, v ? 0 : 1, a, b);
                } else {
                    for (int c = svLow(i, 3); c <= svHigh(i, 3); ++c) {
                        if (dim == 3) {
                            svBit v = svGetBitArrElem(i, a, b, c);
                            svBit v2 = svGetBitArrElem3(i, a, b, c);
                            CHECK_RESULT_HEX(v, v2);
                            svPutBitArrElem(o, v ? 0 : 1, a, b, c);
                            svPutBitArrElem3(q, v ? 0 : 1, a, b, c);
                        }
                    }
                }
            }
        }
    }
    fflush(stdout);
}
void dpii_bit_elem_p0_u1(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                         const svOpenArrayHandle q) {
    _dpii_bit_elem_ux(p, u, i, o, q);
}
void dpii_bit_elem_p0_u2(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                         const svOpenArrayHandle q) {
    _dpii_bit_elem_ux(p, u, i, o, q);
}
void dpii_bit_elem_p0_u3(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                         const svOpenArrayHandle q) {
    _dpii_bit_elem_ux(p, u, i, o, q);
}

//======================================================================

static void _dpii_logic_elem_ux(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                                const svOpenArrayHandle q) {
    int sizeInputOfArray = svSizeOfArray(i);
    int dim = svDimensions(i);
#ifndef NC
    // NC always returns zero and warns
    CHECK_RESULT_HEX(dim, u);
    // svSizeOfArray(i) undeterministic as not in C representation
#endif

    for (int a = svLow(i, 1); a <= svHigh(i, 1); ++a) {
        if (dim == 1) {
            svLogic v = svGetLogicArrElem(i, a);
            svLogic v2 = svGetLogicArrElem1(i, a);
            CHECK_RESULT_HEX(v, v2);
            svPutLogicArrElem(o, v ? 0 : 1, a);
            svPutLogicArrElem1(q, v ? 0 : 1, a);
        } else {
            for (int b = svLow(i, 2); b <= svHigh(i, 2); ++b) {
                if (dim == 2) {
                    svLogic v = svGetLogicArrElem(i, a, b);
                    svLogic v2 = svGetLogicArrElem2(i, a, b);
                    CHECK_RESULT_HEX(v, v2);
                    svPutLogicArrElem(o, v ? 0 : 1, a, b);
                    svPutLogicArrElem2(q, v ? 0 : 1, a, b);
                } else {
                    for (int c = svLow(i, 3); c <= svHigh(i, 3); ++c) {
                        if (dim == 3) {
                            svLogic v = svGetLogicArrElem(i, a, b, c);
                            svLogic v2 = svGetLogicArrElem3(i, a, b, c);
                            CHECK_RESULT_HEX(v, v2);
                            svPutLogicArrElem(o, v ? 0 : 1, a, b, c);
                            svPutLogicArrElem3(q, v ? 0 : 1, a, b, c);
                        }
                    }
                }
            }
        }
    }
    fflush(stdout);
}
void dpii_logic_elem_p0_u1(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                           const svOpenArrayHandle q) {
    _dpii_logic_elem_ux(p, u, i, o, q);
}
void dpii_logic_elem_p0_u2(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                           const svOpenArrayHandle q) {
    _dpii_logic_elem_ux(p, u, i, o, q);
}
void dpii_logic_elem_p0_u3(int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o,
                           const svOpenArrayHandle q) {
    _dpii_logic_elem_ux(p, u, i, o, q);
}
