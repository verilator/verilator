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

#include "svdpi.h"

#include <cstdio>
#include <cstring>
#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

//======================================================================

// clang-format off
#if defined(VERILATOR)
# include "Vt_dpi_open__Dpi.h"
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

extern void dpii_unused(const svOpenArrayHandle u);

extern void dpii_open_p0_u1(int c, int p, int u, const svOpenArrayHandle i,
                            const svOpenArrayHandle o);
extern void dpii_open_p1_u0(int c, int p, int u, const svOpenArrayHandle i,
                            const svOpenArrayHandle o);
extern void dpii_open_p1_u1(int c, int p, int u, const svOpenArrayHandle i,
                            const svOpenArrayHandle o);
extern void dpii_open_p1_u2(int c, int p, int u, const svOpenArrayHandle i,
                            const svOpenArrayHandle o);
extern void dpii_open_p1_u3(int c, int p, int u, const svOpenArrayHandle i,
                            const svOpenArrayHandle o);
extern void dpii_open_pw_u0(int c, int p, int u, const svOpenArrayHandle i,
                            const svOpenArrayHandle o);
extern void dpii_open_pw_u1(int c, int p, int u, const svOpenArrayHandle i,
                            const svOpenArrayHandle o);
extern void dpii_open_pw_u2(int c, int p, int u, const svOpenArrayHandle i,
                            const svOpenArrayHandle o);
extern void dpii_open_pw_u3(int c, int p, int u, const svOpenArrayHandle i,
                            const svOpenArrayHandle o);

extern void dpii_open_bit(const svOpenArrayHandle i, const svOpenArrayHandle o);
extern void dpii_open_byte(const svOpenArrayHandle i, const svOpenArrayHandle o);
extern void dpii_open_int(const svOpenArrayHandle i, const svOpenArrayHandle o);
extern void dpii_open_integer(const svOpenArrayHandle i, const svOpenArrayHandle o);
extern void dpii_open_logic(const svOpenArrayHandle i, const svOpenArrayHandle o);

extern void dpii_open_int_u1(int u, const svOpenArrayHandle i, const svOpenArrayHandle o);
extern void dpii_open_int_u2(int u, const svOpenArrayHandle i, const svOpenArrayHandle o);
extern void dpii_open_int_u3(int u, const svOpenArrayHandle i, const svOpenArrayHandle o);

extern int dpii_failure();
}
#endif

int errors = 0;
int dpii_failure() { return errors; }

void dpii_unused(const svOpenArrayHandle u) {}

void _dpii_all(int c, int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
#ifdef TEST_VERBOSE
    fprintf(stderr, "-:%s:%d: For case c=%d p=%d u=%d  data=%p\n",  //
            __FILE__, __LINE__, c, p, u, svGetArrayPtr(i));
#endif
    (void)svGetArrayPtr(i);
#ifndef NC
    // NC always returns zero and warns
    (void)svSizeOfArray(i);
#endif
#ifndef VCS  // VCS does not support dimension 0 query
    if (p) {
        int d = 0;
        if (c == 0 || c == 1) {
            TEST_CHECK_HEX_EQ(svLeft(i, d), 1);
            TEST_CHECK_HEX_EQ(svRight(i, d), -1);
            TEST_CHECK_HEX_EQ(svLow(i, d), -1);
            TEST_CHECK_HEX_EQ(svHigh(i, d), 1);
            // TEST_CHECK_HEX_EQ(svIncrement(i, d), 0);
            TEST_CHECK_HEX_EQ(svSize(i, d), 3);
        } else if (c == 2) {
            TEST_CHECK_HEX_EQ(svLeft(i, d), 95);
            TEST_CHECK_HEX_EQ(svRight(i, d), 1);
            TEST_CHECK_HEX_EQ(svLow(i, d), 1);
            TEST_CHECK_HEX_EQ(svHigh(i, d), 95);
            // TEST_CHECK_HEX_EQ(svIncrement(i, d), 0);
            TEST_CHECK_HEX_EQ(svSize(i, d), 95);
        } else {
            TEST_CHECK_HEX_EQ(0, 1);
        }
    }
#endif
    if (u >= 1) {
        int d = 1;
        if (c == 0) {
            TEST_CHECK_HEX_EQ(svLeft(i, d), -2);
            TEST_CHECK_HEX_EQ(svRight(i, d), 2);
            TEST_CHECK_HEX_EQ(svLow(i, d), -2);
            TEST_CHECK_HEX_EQ(svHigh(i, d), 2);
            // TEST_CHECK_HEX_EQ(svIncrement(i, d), 0);
            TEST_CHECK_HEX_EQ(svSize(i, d), 5);
        } else if (c == 1) {
            TEST_CHECK_HEX_EQ(svLeft(i, d), 2);
            TEST_CHECK_HEX_EQ(svRight(i, d), -2);
            TEST_CHECK_HEX_EQ(svLow(i, d), -2);
            TEST_CHECK_HEX_EQ(svHigh(i, d), 2);
            // TEST_CHECK_HEX_EQ(svIncrement(i, d), 0);
            TEST_CHECK_HEX_EQ(svSize(i, d), 5);
        }
    }
    if (u >= 2) {
        int d = 2;
        if (c == 0) {
            TEST_CHECK_HEX_EQ(svLeft(i, d), -3);
            TEST_CHECK_HEX_EQ(svRight(i, d), 3);
            TEST_CHECK_HEX_EQ(svLow(i, d), -3);
            TEST_CHECK_HEX_EQ(svHigh(i, d), 3);
            // TEST_CHECK_HEX_EQ(svIncrement(i, d), 0);
            TEST_CHECK_HEX_EQ(svSize(i, d), 7);
        } else if (c == 1) {
            TEST_CHECK_HEX_EQ(svLeft(i, d), 3);
            TEST_CHECK_HEX_EQ(svRight(i, d), -3);
            TEST_CHECK_HEX_EQ(svLow(i, d), -3);
            TEST_CHECK_HEX_EQ(svHigh(i, d), 3);
            // TEST_CHECK_HEX_EQ(svIncrement(i, d), 0);
            TEST_CHECK_HEX_EQ(svSize(i, d), 7);
        }
    }
#ifdef VERILATOR
    // Check out-of-bounds read doesn't access bad memory (when sanitizer used)
    (void)svLeft(i, -1);
    (void)svRight(i, -1);
    (void)svLow(i, -1);
    (void)svHigh(i, -1);
    (void)svIncrement(i, -1);
    (void)svSize(i, -1);
    //
    (void)svLeft(i, 99);
    (void)svRight(i, 99);
    (void)svLow(i, 99);
    (void)svHigh(i, 99);
    (void)svIncrement(i, 99);
    (void)svSize(i, 99);
#endif

    if (c == 2 && p == 1 && u == 3) {
        for (int a = svLow(i, 1); a <= svHigh(i, 1); ++a) {
            for (int b = svLow(i, 2); b <= svHigh(i, 2); ++b) {
                for (int c = svLow(i, 3); c <= svHigh(i, 3); ++c) {
                    // printf("Copy abc %d,%d,%d\n", a,b,c);
                    svLogicVecVal vec[3];
                    svGetLogicArrElemVecVal(vec, i, a, b, c);
#ifdef NC
                    // printf("   %08lx_%08lx_%08lx\n", vec[2].a, vec[1].a, vec[0].a);
                    vec[0].a = (~vec[0].a);
                    vec[1].a = (~vec[1].a);
                    vec[2].a = (~vec[2].a) & 0x7fffffff;
                    // vec[0].b = vec[0].b;
                    // vec[1].b = vec[1].b;
                    // vec[2].b = vec[2].b;
#else
                    vec[0].aval = (~vec[0].aval);
                    vec[1].aval = (~vec[1].aval);
                    vec[2].aval = (~vec[2].aval) & 0x7fffffff;
                    // vec[0].bval = vec[0].bval;
                    // vec[1].bval = vec[1].bval;
                    // vec[2].bval = vec[2].bval;
#endif
                    svPutLogicArrElemVecVal(o, vec, a, b, c);
                }
            }
        }
    }
}

void dpii_open_p0_u1(int c, int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
    _dpii_all(c, p, u, i, o);
}
void dpii_open_p1_u0(int c, int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
    _dpii_all(c, p, u, i, o);
}
void dpii_open_p1_u1(int c, int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
    _dpii_all(c, p, u, i, o);
}
void dpii_open_p1_u2(int c, int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
    _dpii_all(c, p, u, i, o);
}
void dpii_open_p1_u3(int c, int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
    _dpii_all(c, p, u, i, o);
}
void dpii_open_pw_u0(int c, int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
    _dpii_all(c, p, u, i, o);
}
void dpii_open_pw_u1(int c, int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
    _dpii_all(c, p, u, i, o);
}
void dpii_open_pw_u2(int c, int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
    _dpii_all(c, p, u, i, o);
}
void dpii_open_pw_u3(int c, int p, int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
    _dpii_all(c, p, u, i, o);
}

void dpii_open_bit(const svOpenArrayHandle i, const svOpenArrayHandle o) {}

void dpii_open_byte(const svOpenArrayHandle i, const svOpenArrayHandle o) {
    intptr_t arrPtr = (intptr_t)svGetArrayPtr(i);
    TEST_CHECK_HEX_NE(arrPtr, 0);  // All the arrays should actually exist
#ifndef NC
    // NC always returns zero and warns
    int sizeInputOfArray = svSizeOfArray(i);
    TEST_CHECK_HEX_NE(sizeInputOfArray, 0);  // None of the test cases have zero size
    TEST_CHECK_HEX_NE(svDimensions(i), 0);  // All the test cases are unpacked arrays
#endif
}

void dpii_open_integer(const svOpenArrayHandle i, const svOpenArrayHandle o) {}
void dpii_open_logic(const svOpenArrayHandle i, const svOpenArrayHandle o) {}

static void _dpii_open_int_ux(int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
    intptr_t arrPtr = (intptr_t)svGetArrayPtr(i);
    TEST_CHECK_HEX_NE(arrPtr, 0);  // All the arrays should actually exist
#ifndef NC
    // NC always returns zero and warns
    int sizeInputOfArray = svSizeOfArray(i);
    TEST_CHECK_HEX_NE(sizeInputOfArray, 0);  // None of the test cases have zero size
    TEST_CHECK_HEX_EQ(svDimensions(i), u);
#endif

    int dim = svDimensions(i);

    for (int a = svLow(i, 1); a <= svHigh(i, 1); ++a) {
        if (dim == 1) {
            intptr_t ip = (intptr_t)svGetArrElemPtr(i, a);
            intptr_t i2p = (intptr_t)svGetArrElemPtr1(i, a);
            TEST_CHECK_HEX_EQ(ip, i2p);
            TEST_CHECK_HEX_NE(ip, 0);
            intptr_t op = (intptr_t)svGetArrElemPtr(o, a);
            TEST_CHECK_HEX_NE(op, 0);
            *reinterpret_cast<int*>(op) = ~*reinterpret_cast<int*>(ip);
        } else {
            for (int b = svLow(i, 2); b <= svHigh(i, 2); ++b) {
                if (dim == 2) {
                    intptr_t ip = (intptr_t)svGetArrElemPtr(i, a, b);
                    intptr_t i2p = (intptr_t)svGetArrElemPtr2(i, a, b);
                    TEST_CHECK_HEX_EQ(ip, i2p);
                    TEST_CHECK_HEX_NE(ip, 0);
                    intptr_t op = (intptr_t)svGetArrElemPtr(o, a, b);
                    TEST_CHECK_HEX_NE(op, 0);
                    *reinterpret_cast<int*>(op) = ~*reinterpret_cast<int*>(ip);
                } else {
                    for (int c = svLow(i, 3); c <= svHigh(i, 3); ++c) {
                        if (dim == 3) {
                            intptr_t ip = (intptr_t)svGetArrElemPtr(i, a, b, c);
                            intptr_t i2p = (intptr_t)svGetArrElemPtr3(i, a, b, c);
                            TEST_CHECK_HEX_EQ(ip, i2p);
                            TEST_CHECK_HEX_NE(ip, 0);
                            intptr_t op = (intptr_t)svGetArrElemPtr(o, a, b, c);
                            TEST_CHECK_HEX_NE(op, 0);
                            *reinterpret_cast<int*>(op) = ~*reinterpret_cast<int*>(ip);
                        }
                    }
                }
            }
        }
    }
}
void dpii_open_int_u1(int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
    _dpii_open_int_ux(u, i, o);
}
void dpii_open_int_u2(int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
    _dpii_open_int_ux(u, i, o);
}
void dpii_open_int_u3(int u, const svOpenArrayHandle i, const svOpenArrayHandle o) {
    _dpii_open_int_ux(u, i, o);
}
