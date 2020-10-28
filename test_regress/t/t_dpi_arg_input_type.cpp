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

#include <cstdio>
#include <cstdlib>
#include <cstring>

// clang-format off
#if defined(NCSC)
// Used by NC's svdpi.h to pick up svLogicVecVal with _.aval and _.bval fields,
// rather than the IEEE 1800-2005 version which has _.a and _.b fields.
# define DPI_COMPATIBILITY_VERSION_1800v2012
#endif

#include "svdpi.h"

#if defined(VERILATOR)  // Verilator
# include "Vt_dpi_arg_input_type__Dpi.h"
typedef long long sv_longint_t;
typedef unsigned long long sv_longint_unsigned_t;
# define NO_SHORTREAL
# define CONSTARG const
#elif defined(VCS)  // VCS
# include "../vc_hdrs.h"
typedef long long sv_longint_t;
typedef unsigned long long sv_longint_unsigned_t;
# define NO_TIME
# define CONSTARG const
#elif defined(NCSC)  // NC
# include "dpi-exp.h"
# include "dpi-imp.h"
typedef long long sv_longint_t;
typedef unsigned long long sv_longint_unsigned_t;
# define NO_TIME
# define NO_INTEGER
# define NO_SHORTREAL
// Sadly NC does not declare pass-by reference input arguments as const
# define CONSTARG
#elif defined(MS)  // ModelSim
# include "dpi.h"
typedef int64_t sv_longint_t;
typedef uint64_t sv_longint_unsigned_t;
# define CONSTARG const
#else
# error "Unknown simulator for DPI test"
#endif
// clang-format on

//======================================================================
// Implementations of imported functions
//======================================================================

#define stop() \
    do { \
        printf(__FILE__ ":%d Bad value\n", __LINE__); \
        abort(); \
    } while (0)

void check_bvals(CONSTARG svLogicVecVal* v, unsigned n);
void check_bvals(CONSTARG svLogicVecVal* v, unsigned n) {
    for (unsigned i = 0; i < n; i++) {
        if (v[i].bval != 0) {
            printf(__FILE__ ":%d Bad svLogicVecVal bval\n", __LINE__);
            abort();
        }
    }
}

// Basic types as per IEEE 1800-2017 35.5.6
void i_byte(char i) {
    static int n = 0;
    if (i != 10 - n++) stop();
}

void i_byte_unsigned(unsigned char i) {
    static int n = 0;
    if (i != 20 - n++) stop();
}

void i_shortint(short i) {
    static int n = 0;
    if (i != 30 - n++) stop();
}

void i_shortint_unsigned(unsigned short i) {
    static int n = 0;
    if (i != 40 - n++) stop();
}

void i_int(int i) {
    static int n = 0;
    if (i != 50 - n++) stop();
}

void i_int_unsigned(unsigned i) {
    static int n = 0;
    if (i != 60 - n++) stop();
}

void i_longint(sv_longint_t i) {
    static int n = 0;
    if (i != 70 - n++) stop();
}

void i_longint_unsigned(sv_longint_unsigned_t i) {
    static int n = 0;
    if (i != 80 - n++) stop();
}

#ifndef NO_TIME
void i_time(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    if (i[0].aval != 90 - n++) stop();
    if (i[1].aval != 0) stop();
    check_bvals(i, 2);
}
#endif

#ifndef NO_INTEGER
void i_integer(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    if (i[0].aval != 100 - n++) stop();
    check_bvals(i, 1);
}
#endif

void i_real(double i) {
    static int n = 0;
    if (i != (-2.0 * n++ - 1.0) / 2.0) stop();
}

#ifndef NO_SHORTREAL
void i_shortreal(float i) {
    static int n = 0;
    if (i != (-4.0f * n++ - 1.0f) / 4.0f) stop();
}
#endif

void i_chandle(void* i) {
    static int n = 0;
    printf("i_chandle %d\n", n);
    if (i) stop();
    n++;
}

void i_string(const char* i) {
    static int n = 0;
    printf("i_string %d\n", n);
    if (n++ % 2 == 0) {
        if (strcmp(i, "World") != 0) stop();
    } else {
        if (strcmp(i, "Hello") != 0) stop();
    }
}

void i_bit(svBit i) {
    static int n = 0;
    printf("i_bit %d\n", n);
    if (i != !(n++ % 2)) stop();
}

void i_logic(svLogic i) {
    static int n = 0;
    printf("i_logic %d\n", n);
    if (i != n++ % 2) stop();
}

// Basic types via typedefs
void i_byte_t(char i) {
    static int n = 0;
    if (i != 10 - n) stop();
    n += 2;
}

void i_byte_unsigned_t(unsigned char i) {
    static int n = 0;
    if (i != 20 - n) stop();
    n += 2;
}

void i_shortint_t(short i) {
    static int n = 0;
    if (i != 30 - n) stop();
    n += 2;
}

void i_shortint_unsigned_t(unsigned short i) {
    static int n = 0;
    if (i != 40 - n) stop();
    n += 2;
}

void i_int_t(int i) {
    static int n = 0;
    if (i != 50 - n) stop();
    n += 2;
}

void i_int_unsigned_t(unsigned i) {
    static int n = 0;
    if (i != 60 - n) stop();
    n += 2;
}

void i_longint_t(sv_longint_t i) {
    static int n = 0;
    if (i != 70 - n) stop();
    n += 2;
}

void i_longint_unsigned_t(sv_longint_unsigned_t i) {
    static int n = 0;
    if (i != 80 - n) stop();
    n += 2;
}

#ifndef NO_TIME
void i_time_t(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    if (i[0].aval != 90 - n) stop();
    if (i[1].aval != 0) stop();
    check_bvals(i, 2);
    n += 2;
}
#endif

#ifndef NO_INTEGER
void i_integer_t(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    if (i[0].aval != 100 - n) stop();
    check_bvals(i, 1);
    n += 2;
}
#endif

void i_real_t(double i) {
    static int n = 0;
    if (i != (-2.0 * n - 1.0) / 2.0) stop();
    n += 2;
}

#ifndef NO_SHORTREAL
void i_shortreal_t(float i) {
    static int n = 0;
    if (i != (-4.0f * n - 1.0f) / 4.0f) stop();
    n += 2;
}
#endif

void i_chandle_t(void* i) {
    static int n = 0;
    printf("i_chandle_t %d\n", n);
    if (i) stop();
    n++;
}

void i_string_t(const char* i) {
    static int n = 0;
    printf("i_string_t %d\n", n);
    if (n++ % 2 == 0) {
        if (strcmp(i, "World") != 0) stop();
    } else {
        if (strcmp(i, "Hello") != 0) stop();
    }
}

void i_bit_t(svBit i) {
    static int n = 0;
    printf("i_bit_t %d\n", n);
    if (i != !(n++ % 2)) stop();
}

void i_logic_t(svLogic i) {
    static int n = 0;
    printf("i_logic_t %d\n", n);
    if (i != n++ % 2) stop();
}

// 2-state packed arrays
void i_array_2_state_1(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_array_2_state_1 %d\n", n);
    if ((*i & 1) != !(n++ % 2)) stop();
}

void i_array_2_state_32(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_array_2_state_32 %d\n", n);
    if (*i != 0xffffffffU << n++) stop();
}

void i_array_2_state_33(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_array_2_state_33 %d\n", n);
    if (i[0] != 0xffffffffU << n++) stop();
    if ((i[1] & 1) != 1) stop();
}

void i_array_2_state_64(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_array_2_state_64 %d\n", n);
    if (i[0] != 0xffffffffU << n++) stop();
    if (i[1] != -1) stop();
}

void i_array_2_state_65(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_array_2_state_65 %d\n", n);
    if (i[0] != 0xffffffffU << n++) stop();
    if (i[1] != -1) stop();
    if ((i[2] & 1) != 1) stop();
}

void i_array_2_state_128(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_array_2_state_128 %d\n", n);
    if (i[0] != 0xffffffffU << n++) stop();
    if (i[1] != -1) stop();
    if (i[2] != -1) stop();
    if (i[3] != -1) stop();
}

// 2-state packed structures
void i_struct_2_state_1(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_struct_2_state_1 %d\n", n);
    if ((*i & 1) != !(n++ % 2)) stop();
}

void i_struct_2_state_32(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_struct_2_state_32 %d\n", n);
    if (*i != 0xffffffffU << n++) stop();
}

void i_struct_2_state_33(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_struct_2_state_33 %d\n", n);
    if (i[0] != 0xffffffffU << n++) stop();
    if ((i[1] & 1) != 1) stop();
}

void i_struct_2_state_64(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_struct_2_state_64 %d\n", n);
    if (i[0] != 0xffffffffU << n++) stop();
    if (i[1] != -1) stop();
}

void i_struct_2_state_65(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_struct_2_state_65 %d\n", n);
    if (i[0] != 0xffffffffU << n++) stop();
    if (i[1] != -1) stop();
    if ((i[2] & 1) != 1) stop();
}

void i_struct_2_state_128(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_struct_2_state_128 %d\n", n);
    if (i[0] != 0xffffffffU << n++) stop();
    if (i[1] != -1) stop();
    if (i[2] != -1) stop();
    if (i[3] != -1) stop();
}

// 2-state packed unions
void i_union_2_state_1(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_union_2_state_1 %d\n", n);
    if ((*i & 1) != !(n++ % 2)) stop();
}

void i_union_2_state_32(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_union_2_state_32 %d\n", n);
    if (*i != 0xffffffffU << n++) stop();
}

void i_union_2_state_33(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_union_2_state_33 %d\n", n);
    if (i[0] != 0xffffffffU << n++) stop();
    if ((i[1] & 1) != 1) stop();
}

void i_union_2_state_64(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_union_2_state_64 %d\n", n);
    if (i[0] != 0xffffffffU << n++) stop();
    if (i[1] != -1) stop();
}

void i_union_2_state_65(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_union_2_state_65 %d\n", n);
    if (i[0] != 0xffffffffU << n++) stop();
    if (i[1] != -1) stop();
    if ((i[2] & 1) != 1) stop();
}

void i_union_2_state_128(CONSTARG svBitVecVal* i) {
    static int n = 0;
    printf("i_union_2_state_128 %d\n", n);
    if (i[0] != 0xffffffffU << n++) stop();
    if (i[1] != -1) stop();
    if (i[2] != -1) stop();
    if (i[3] != -1) stop();
}

// 4-state packed arrays
void i_array_4_state_1(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_array_4_state_1 %d\n", n);
    if ((i->aval & 1) != !(n++ % 2)) stop();
    check_bvals(i, 1);
}

void i_array_4_state_32(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_array_4_state_32 %d\n", n);
    if (i->aval != 0xffffffffU << n++) stop();
    check_bvals(i, 1);
}

void i_array_4_state_33(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_array_4_state_33 %d\n", n);
    if (i[0].aval != 0xffffffffU << n++) stop();
    if ((i[1].aval & 1) != 1) stop();
    check_bvals(i, 2);
}

void i_array_4_state_64(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_array_4_state_64 %d\n", n);
    if (i[0].aval != 0xffffffffU << n++) stop();
    if (i[1].aval != -1) stop();
    check_bvals(i, 2);
}

void i_array_4_state_65(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_array_4_state_65 %d\n", n);
    if (i[0].aval != 0xffffffffU << n++) stop();
    if (i[1].aval != -1) stop();
    if ((i[2].aval & 1) != 1) stop();
    check_bvals(i, 3);
}

void i_array_4_state_128(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_array_4_state_128 %d\n", n);
    if (i[0].aval != 0xffffffffU << n++) stop();
    if (i[1].aval != -1) stop();
    if (i[2].aval != -1) stop();
    if (i[3].aval != -1) stop();
    check_bvals(i, 4);
}

// 4-state packed structures
void i_struct_4_state_1(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_struct_4_state_1 %d\n", n);
    if ((i->aval & 1) != !(n++ % 2)) stop();
    check_bvals(i, 1);
}

void i_struct_4_state_32(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_struct_4_state_32 %d\n", n);
    if (i->aval != 0xffffffffU << n++) stop();
    check_bvals(i, 1);
}

void i_struct_4_state_33(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_struct_4_state_33 %d\n", n);
    if (i[0].aval != 0xffffffffU << n++) stop();
    if ((i[1].aval & 1) != 1) stop();
    check_bvals(i, 2);
}

void i_struct_4_state_64(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_struct_4_state_64 %d\n", n);
    if (i[0].aval != 0xffffffffU << n++) stop();
    if (i[1].aval != -1) stop();
    check_bvals(i, 2);
}

void i_struct_4_state_65(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_struct_4_state_65 %d\n", n);
    if (i[0].aval != 0xffffffffU << n++) stop();
    if (i[1].aval != -1) stop();
    if ((i[2].aval & 1) != 1) stop();
    check_bvals(i, 3);
}

void i_struct_4_state_128(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_struct_4_state_128 %d\n", n);
    if (i[0].aval != 0xffffffffU << n++) stop();
    if (i[1].aval != -1) stop();
    if (i[2].aval != -1) stop();
    if (i[3].aval != -1) stop();
    check_bvals(i, 4);
}

// 4-state packed unions
void i_union_4_state_1(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_union_4_state_1 %d\n", n);
    if ((i->aval & 1) != !(n++ % 2)) stop();
    check_bvals(i, 1);
}

void i_union_4_state_32(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_union_4_state_32 %d\n", n);
    if (i->aval != 0xffffffffU << n++) stop();
    check_bvals(i, 1);
}

void i_union_4_state_33(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_union_4_state_33 %d\n", n);
    if (i[0].aval != 0xffffffffU << n++) stop();
    if ((i[1].aval & 1) != 1) stop();
    check_bvals(i, 2);
}

void i_union_4_state_64(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_union_4_state_64 %d\n", n);
    if (i[0].aval != 0xffffffffU << n++) stop();
    if (i[1].aval != -1) stop();
    check_bvals(i, 2);
}

void i_union_4_state_65(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_union_4_state_65 %d\n", n);
    if (i[0].aval != 0xffffffffU << n++) stop();
    if (i[1].aval != -1) stop();
    if ((i[2].aval & 1) != 1) stop();
    check_bvals(i, 3);
}

void i_union_4_state_128(CONSTARG svLogicVecVal* i) {
    static int n = 0;
    printf("i_union_4_state_128 %d\n", n);
    if (i[0].aval != 0xffffffffU << n++) stop();
    if (i[1].aval != -1) stop();
    if (i[2].aval != -1) stop();
    if (i[3].aval != -1) stop();
    check_bvals(i, 4);
}

//======================================================================
// Check exported functions
//======================================================================

void set_bvals(svLogicVecVal* v, unsigned n);
void set_bvals(svLogicVecVal* v, unsigned n) {
    for (unsigned i = 0; i < n; i++) v[i].bval = 0;
}

void check_exports() {
    static int n = 0;

#ifndef NO_TIME
    svLogicVecVal x_time[2];
    svLogicVecVal x_time_t[2];
#endif
#ifndef NO_INTEGER
    svLogicVecVal x_integer[1];
    svLogicVecVal x_integer_t[1];
#endif

#ifndef NO_TIME
    set_bvals(x_time, 2);
    set_bvals(x_time_t, 2);
#endif
#ifndef NO_INTEGER
    set_bvals(x_integer, 1);
    set_bvals(x_integer_t, 1);
#endif

    // Basic types as per IEEE 1800-2017 35.5.6
    e_byte(10 + n);
    e_byte_unsigned(20 + n);
    e_shortint(30 + n);
    e_shortint_unsigned(40 + n);
    e_int(50 + n);
    e_int_unsigned(60 + n);
    e_longint(70 + n);
    e_longint_unsigned(80 + n);
#ifndef NO_TIME
    x_time[0].aval = 90 + n;
    x_time[1].aval = 0;
    e_time(x_time);
#endif
#ifndef NO_INTEGER
    x_integer[0].aval = 100 + n;
    e_integer(x_integer);
#endif
    e_real(1.0 * n + 0.5);
#ifndef NO_SHORTREAL
    e_shortreal(1.0f * n + 0.25f);
#endif
    e_chandle((n % 2) ? reinterpret_cast<void*>(&e_chandle) : NULL);
    e_string((n % 2) ? "World" : "Hello");
    e_bit(n % 2);
    e_logic(!(n % 2));

    // Basic types via tyepdef
    e_byte_t(10 + 2 * n);
    e_byte_unsigned_t(20 + 2 * n);
    e_shortint_t(30 + 2 * n);
    e_shortint_unsigned_t(40 + 2 * n);
    e_int_t(50 + 2 * n);
    e_int_unsigned_t(60 + 2 * n);
    e_longint_t(70 + 2 * n);
    e_longint_unsigned_t(80 + 2 * n);
#ifndef NO_TIME
    x_time_t[0].aval = 90 + 2 * n;
    x_time_t[1].aval = 0;
    e_time_t(x_time_t);
#endif
#ifndef NO_INTEGER
    x_integer_t[0].aval = 100 + 2 * n;
    e_integer_t(x_integer_t);
#endif
    e_real_t(1.0 * (2 * n) + 0.5);
#ifndef NO_SHORTREAL
    e_shortreal_t(1.0f * (2 * n) + 0.25f);
#endif
    e_chandle_t((n % 2) ? NULL : reinterpret_cast<void*>(&e_chandle_t));
    e_string_t((n % 2) ? "Hello" : "World");
    e_bit_t(n % 2);
    e_logic_t(!(n % 2));

    const int m = n == 0 ? 0 : n - 1;

    svBitVecVal b1[1];
    svBitVecVal b2[2];
    svBitVecVal b3[3];
    svBitVecVal b4[4];

    b3[0] = 0xffffffff;
    b4[0] = 0xffffffff;
    b4[1] = 0xffffffff;
    b4[2] = 0xffffffff;

    // 2-state packed arrays
    b1[0] = n % 2;
    e_array_2_state_1(b1);

    b1[0] = 0xffffffff >> n;
    e_array_2_state_32(b1);

    b2[1] = 1 >> n;
    b2[0] = 0xffffffff >> m;
    e_array_2_state_33(b2);

    b2[1] = 0xffffffff >> n;
    b2[0] = 0xffffffff;
    e_array_2_state_64(b2);

    b3[2] = 1 >> n;
    b3[1] = 0xffffffff >> m;
    e_array_2_state_65(b3);

    b4[3] = 0xffffffff >> n;
    e_array_2_state_128(b4);

    // 2-state packed structures
    b1[0] = n % 2;
    e_struct_2_state_1(b1);

    b1[0] = 0xffffffff >> n;
    e_struct_2_state_32(b1);

    b2[1] = 1 >> n;
    b2[0] = 0xffffffff >> m;
    e_struct_2_state_33(b2);

    b2[1] = 0xffffffff >> n;
    b2[0] = 0xffffffff;
    e_struct_2_state_64(b2);

    b3[2] = 1 >> n;
    b3[1] = 0xffffffff >> m;
    e_struct_2_state_65(b3);

    b4[3] = 0xffffffff >> n;
    e_struct_2_state_128(b4);

    // 2-state packed unions
    b1[0] = n % 2;
    e_union_2_state_1(b1);

    b1[0] = 0xffffffff >> n;
    e_union_2_state_32(b1);

    b2[1] = 1 >> n;
    b2[0] = 0xffffffff >> m;
    e_union_2_state_33(b2);

    b2[1] = 0xffffffff >> n;
    b2[0] = 0xffffffff;
    e_union_2_state_64(b2);

    b3[2] = 1 >> n;
    b3[1] = 0xffffffff >> m;
    e_union_2_state_65(b3);

    b4[3] = 0xffffffff >> n;
    e_union_2_state_128(b4);

    svLogicVecVal l1[1];
    svLogicVecVal l2[2];
    svLogicVecVal l3[3];
    svLogicVecVal l4[4];

    // bvals should be ignored, leave them un-initialized

    set_bvals(l1, 1);
    set_bvals(l2, 2);
    set_bvals(l3, 3);
    set_bvals(l4, 4);

    l3[0].aval = 0xffffffff;
    l4[0].aval = 0xffffffff;
    l4[1].aval = 0xffffffff;
    l4[2].aval = 0xffffffff;

    // 4-state packed arrays
    l1[0].aval = n % 2;
    e_array_4_state_1(l1);

    l1[0].aval = 0xffffffff >> n;
    e_array_4_state_32(l1);

    l2[1].aval = 1 >> n;
    l2[0].aval = 0xffffffff >> m;
    e_array_4_state_33(l2);

    l2[1].aval = 0xffffffff >> n;
    l2[0].aval = 0xffffffff;
    e_array_4_state_64(l2);

    l3[2].aval = 1 >> n;
    l3[1].aval = 0xffffffff >> m;
    e_array_4_state_65(l3);

    l4[3].aval = 0xffffffff >> n;
    e_array_4_state_128(l4);

    // 4-state packed structures
    l1[0].aval = n % 2;
    e_struct_4_state_1(l1);

    l1[0].aval = 0xffffffff >> n;
    e_struct_4_state_32(l1);

    l2[1].aval = 1 >> n;
    l2[0].aval = 0xffffffff >> m;
    e_struct_4_state_33(l2);

    l2[1].aval = 0xffffffff >> n;
    l2[0].aval = 0xffffffff;
    e_struct_4_state_64(l2);

    l3[2].aval = 1 >> n;
    l3[1].aval = 0xffffffff >> m;
    e_struct_4_state_65(l3);

    l4[3].aval = 0xffffffff >> n;
    e_struct_4_state_128(l4);

    // 4-state packed unions
    l1[0].aval = n % 2;
    e_union_4_state_1(l1);

    l1[0].aval = 0xffffffff >> n;
    e_union_4_state_32(l1);

    l2[1].aval = 1 >> n;
    l2[0].aval = 0xffffffff >> m;
    e_union_4_state_33(l2);

    l2[1].aval = 0xffffffff >> n;
    l2[0].aval = 0xffffffff;
    e_union_4_state_64(l2);

    l3[2].aval = 1 >> n;
    l3[1].aval = 0xffffffff >> m;
    e_union_4_state_65(l3);

    l4[3].aval = 0xffffffff >> n;
    e_union_4_state_128(l4);

    n++;
}
