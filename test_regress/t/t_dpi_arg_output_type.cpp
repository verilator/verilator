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
# include "Vt_dpi_arg_output_type__Dpi.h"
typedef long long sv_longint_t;
typedef unsigned long long sv_longint_unsigned_t;
# define NO_SHORTREAL
#elif defined(VCS)  // VCS
# include "../vc_hdrs.h"
typedef long long sv_longint_t;
typedef unsigned long long sv_longint_unsigned_t;
# define NO_TIME
#elif defined(NCSC)  // NC
# include "dpi-exp.h"
# include "dpi-imp.h"
typedef long long sv_longint_t;
typedef unsigned long long sv_longint_unsigned_t;
# define NO_TIME
# define NO_INTEGER
# define NO_SHORTREAL
#elif defined(MS)  // ModelSim
# include "dpi.h"
typedef int64_t sv_longint_t;
typedef uint64_t sv_longint_unsigned_t;
# else
# error "Unknown simulator for DPI test"
#endif
// clang-format on

//======================================================================
// Implementations of imported functions
//======================================================================

void set_bvals(svLogicVecVal* v, unsigned n);
void set_bvals(svLogicVecVal* v, unsigned n) {
    for (unsigned i = 0; i < n; i++) v[i].bval = 0;
}

// Basic types as per IEEE 1800-2017 35.5.6
void i_byte(char* o) {
    static int n = 0;
    *o = 10 - n++;
}

void i_byte_unsigned(unsigned char* o) {
    static int n = 0;
    *o = 20 - n++;
}

void i_shortint(short* o) {
    static int n = 0;
    *o = 30 - n++;
}

void i_shortint_unsigned(unsigned short* o) {
    static int n = 0;
    *o = 40 - n++;
}

void i_int(int* o) {
    static int n = 0;
    *o = 50 - n++;
}

void i_int_unsigned(unsigned* o) {
    static int n = 0;
    *o = 60 - n++;
}

void i_longint(sv_longint_t* o) {
    static int n = 0;
    *o = 70 - n++;
}

void i_longint_unsigned(sv_longint_unsigned_t* o) {
    static int n = 0;
    *o = 80 - n++;
}

#ifndef NO_TIME
void i_time(svLogicVecVal* o) {
    static int n = 0;
    o[0].aval = 90 - n++;
    o[1].aval = 0;
    set_bvals(o, 2);
}
#endif

#ifndef NO_INTEGER
void i_integer(svLogicVecVal* o) {
    static int n = 0;
    o->aval = 100 - n++;
    set_bvals(o, 1);
}
#endif

void i_real(double* o) {
    static int n = 0;
    *o = (-2.0 * n++ - 1.0) / 2.0;
}

#ifndef NO_SHORTREAL
void i_shortreal(float* o) {
    static int n = 0;
    *o = (-4.0f * n++ - 1.0f) / 4.0f;
}
#endif

void i_chandle(void** o) {
    static int n = 0;
    printf("i_chandle %d\n", n);
    *o = (n++ % 2) ? reinterpret_cast<void*>(&i_chandle) : NULL;
}

void i_string(const char** o) {
    static int n = 0;
    printf("i_string %d\n", n);
    *o = (n++ % 2) ? "Hello" : "World";
}

void i_bit(svBit* o) {
    static int n = 0;
    printf("i_bit %d\n", n);
    *o = !(n++ % 2);
}

void i_logic(svLogic* o) {
    static int n = 0;
    printf("i_logic %d\n", n);
    *o = n++ % 2;
}

// Basic types via typedefs
void i_byte_t(char* o) {
    static int n = 0;
    const char r = 10 - n;
    n += 2;
    *o = r;
}

void i_byte_unsigned_t(unsigned char* o) {
    static int n = 0;
    const unsigned char r = 20 - n;
    n += 2;
    *o = r;
}

void i_shortint_t(short* o) {
    static int n = 0;
    const short r = 30 - n;
    n += 2;
    *o = r;
}

void i_shortint_unsigned_t(unsigned short* o) {
    static int n = 0;
    const unsigned short r = 40 - n;
    n += 2;
    *o = r;
}

void i_int_t(int* o) {
    static int n = 0;
    const int r = 50 - n;
    n += 2;
    *o = r;
}

void i_int_unsigned_t(unsigned* o) {
    static int n = 0;
    const unsigned r = 60 - n;
    n += 2;
    *o = r;
}

void i_longint_t(sv_longint_t* o) {
    static int n = 0;
    const long long r = 70 - n;
    n += 2;
    *o = r;
}

void i_longint_unsigned_t(sv_longint_unsigned_t* o) {
    static int n = 0;
    const unsigned long long r = 80 - n;
    n += 2;
    *o = r;
}

#ifndef NO_TIME
void i_time_t(svLogicVecVal* o) {
    static int n = 0;
    o[0].aval = 90 - n;
    o[1].aval = 0;
    set_bvals(o, 2);
    n += 2;
}
#endif

#ifndef NO_INTEGER
void i_integer_t(svLogicVecVal* o) {
    static int n = 0;
    o->aval = 100 - n;
    set_bvals(o, 1);
    n += 2;
}
#endif

void i_real_t(double* o) {
    static int n = 0;
    const double r = (-2.0 * n - 1.0) / 2.0;
    n += 2;
    *o = r;
}

#ifndef NO_SHORTREAL
void i_shortreal_t(float* o) {
    static int n = 0;
    const float r = (-4.0f * n - 1.0f) / 4.0f;
    n += 2;
    *o = r;
}
#endif

void i_chandle_t(void** o) {
    static int n = 0;
    printf("i_chandle_t %d\n", n);
    *o = (n++ % 2) ? reinterpret_cast<void*>(&i_chandle) : NULL;
}

void i_string_t(const char** o) {
    static int n = 0;
    printf("i_string_t %d\n", n);
    *o = (n++ % 2) ? "Hello" : "World";
}

void i_bit_t(svBit* o) {
    static int n = 0;
    printf("i_bit_t %d\n", n);
    *o = !(n++ % 2);
}

void i_logic_t(svLogic* o) {
    static int n = 0;
    printf("i_logic_t %d\n", n);
    *o = n++ % 2;
}

// 2-state packed arrays
void i_array_2_state_1(svBitVecVal* o) {
    static int n = 0;
    printf("i_array_2_state_1 %d\n", n);
    *o = !(n++ % 2);
}

void i_array_2_state_32(svBitVecVal* o) {
    static int n = 0;
    printf("i_array_2_state_32 %d\n", n);
    *o = 0xffffffffU << n++;
}

void i_array_2_state_33(svBitVecVal* o) {
    static int n = 0;
    printf("i_array_2_state_33 %d\n", n);
    o[0] = 0xffffffffU << n++;
    o[1] = 1;
}

void i_array_2_state_64(svBitVecVal* o) {
    static int n = 0;
    printf("i_array_2_state_64 %d\n", n);
    o[0] = 0xffffffffU << n++;
    o[1] = -1;
}

void i_array_2_state_65(svBitVecVal* o) {
    static int n = 0;
    printf("i_array_2_state_65 %d\n", n);
    o[0] = 0xffffffffU << n++;
    o[1] = -1;
    o[2] = 1;
}

void i_array_2_state_128(svBitVecVal* o) {
    static int n = 0;
    printf("i_array_2_state_128 %d\n", n);
    o[0] = 0xffffffffU << n++;
    o[1] = -1;
    o[2] = -1;
    o[3] = -1;
}

// 2-state packed structures
void i_struct_2_state_1(svBitVecVal* o) {
    static int n = 0;
    printf("i_struct_2_state_1 %d\n", n);
    *o = !(n++ % 2);
}

void i_struct_2_state_32(svBitVecVal* o) {
    static int n = 0;
    printf("i_struct_2_state_32 %d\n", n);
    *o = 0xffffffffU << n++;
}

void i_struct_2_state_33(svBitVecVal* o) {
    static int n = 0;
    printf("i_struct_2_state_33 %d\n", n);
    o[0] = 0xffffffffU << n++;
    o[1] = 1;
}

void i_struct_2_state_64(svBitVecVal* o) {
    static int n = 0;
    printf("i_struct_2_state_64 %d\n", n);
    o[0] = 0xffffffffU << n++;
    o[1] = -1;
}

void i_struct_2_state_65(svBitVecVal* o) {
    static int n = 0;
    printf("i_struct_2_state_65 %d\n", n);
    o[0] = 0xffffffffU << n++;
    o[1] = -1;
    o[2] = 1;
}

void i_struct_2_state_128(svBitVecVal* o) {
    static int n = 0;
    printf("i_struct_2_state_128 %d\n", n);
    o[0] = 0xffffffffU << n++;
    o[1] = -1;
    o[2] = -1;
    o[3] = -1;
}

// 2-state packed unions
void i_union_2_state_1(svBitVecVal* o) {
    static int n = 0;
    printf("i_union_2_state_1 %d\n", n);
    *o = !(n++ % 2);
}

void i_union_2_state_32(svBitVecVal* o) {
    static int n = 0;
    printf("i_union_2_state_32 %d\n", n);
    *o = 0xffffffffU << n++;
}

void i_union_2_state_33(svBitVecVal* o) {
    static int n = 0;
    printf("i_union_2_state_33 %d\n", n);
    o[0] = 0xffffffffU << n++;
    o[1] = 1;
}

void i_union_2_state_64(svBitVecVal* o) {
    static int n = 0;
    printf("i_union_2_state_64 %d\n", n);
    o[0] = 0xffffffffU << n++;
    o[1] = -1;
}

void i_union_2_state_65(svBitVecVal* o) {
    static int n = 0;
    printf("i_union_2_state_65 %d\n", n);
    o[0] = 0xffffffffU << n++;
    o[1] = -1;
    o[2] = 1;
}

void i_union_2_state_128(svBitVecVal* o) {
    static int n = 0;
    printf("i_union_2_state_128 %d\n", n);
    o[0] = 0xffffffffU << n++;
    o[1] = -1;
    o[2] = -1;
    o[3] = -1;
}

// 4-state packed arrays
void i_array_4_state_1(svLogicVecVal* o) {
    static int n = 0;
    printf("i_array_4_state_1 %d\n", n);
    o->aval = !(n++ % 2);
    set_bvals(o, 1);
}

void i_array_4_state_32(svLogicVecVal* o) {
    static int n = 0;
    printf("i_array_4_state_32 %d\n", n);
    o->aval = 0xffffffffU << n++;
    set_bvals(o, 1);
}

void i_array_4_state_33(svLogicVecVal* o) {
    static int n = 0;
    printf("i_array_4_state_33 %d\n", n);
    o[0].aval = 0xffffffffU << n++;
    o[1].aval = 1;
    set_bvals(o, 2);
}

void i_array_4_state_64(svLogicVecVal* o) {
    static int n = 0;
    printf("i_array_4_state_64 %d\n", n);
    o[0].aval = 0xffffffffU << n++;
    o[1].aval = -1;
    set_bvals(o, 2);
}

void i_array_4_state_65(svLogicVecVal* o) {
    static int n = 0;
    printf("i_array_4_state_65 %d\n", n);
    o[0].aval = 0xffffffffU << n++;
    o[1].aval = -1;
    o[2].aval = 1;
    set_bvals(o, 3);
}

void i_array_4_state_128(svLogicVecVal* o) {
    static int n = 0;
    printf("i_array_4_state_128 %d\n", n);
    o[0].aval = 0xffffffffU << n++;
    o[1].aval = -1;
    o[2].aval = -1;
    o[3].aval = -1;
    set_bvals(o, 4);
}

// 4-state packed structures
void i_struct_4_state_1(svLogicVecVal* o) {
    static int n = 0;
    printf("i_struct_4_state_1 %d\n", n);
    o->aval = !(n++ % 2);
    set_bvals(o, 1);
}

void i_struct_4_state_32(svLogicVecVal* o) {
    static int n = 0;
    printf("i_struct_4_state_32 %d\n", n);
    o->aval = 0xffffffffU << n++;
    set_bvals(o, 1);
}

void i_struct_4_state_33(svLogicVecVal* o) {
    static int n = 0;
    printf("i_struct_4_state_33 %d\n", n);
    o[0].aval = 0xffffffffU << n++;
    o[1].aval = 1;
    set_bvals(o, 2);
}

void i_struct_4_state_64(svLogicVecVal* o) {
    static int n = 0;
    printf("i_struct_4_state_64 %d\n", n);
    o[0].aval = 0xffffffffU << n++;
    o[1].aval = -1;
    set_bvals(o, 2);
}

void i_struct_4_state_65(svLogicVecVal* o) {
    static int n = 0;
    printf("i_struct_4_state_65 %d\n", n);
    o[0].aval = 0xffffffffU << n++;
    o[1].aval = -1;
    o[2].aval = 1;
    set_bvals(o, 3);
}

void i_struct_4_state_128(svLogicVecVal* o) {
    static int n = 0;
    printf("i_struct_4_state_128 %d\n", n);
    o[0].aval = 0xffffffffU << n++;
    o[1].aval = -1;
    o[2].aval = -1;
    o[3].aval = -1;
    set_bvals(o, 4);
}

// 4-state packed unions
void i_union_4_state_1(svLogicVecVal* o) {
    static int n = 0;
    printf("i_union_4_state_1 %d\n", n);
    o->aval = !(n++ % 2);
    set_bvals(o, 1);
}

void i_union_4_state_32(svLogicVecVal* o) {
    static int n = 0;
    printf("i_union_4_state_32 %d\n", n);
    o->aval = 0xffffffffU << n++;
    set_bvals(o, 1);
}

void i_union_4_state_33(svLogicVecVal* o) {
    static int n = 0;
    printf("i_union_4_state_33 %d\n", n);
    o[0].aval = 0xffffffffU << n++;
    o[1].aval = 1;
    set_bvals(o, 2);
}

void i_union_4_state_64(svLogicVecVal* o) {
    static int n = 0;
    printf("i_union_4_state_64 %d\n", n);
    o[0].aval = 0xffffffffU << n++;
    o[1].aval = -1;
    set_bvals(o, 2);
}

void i_union_4_state_65(svLogicVecVal* o) {
    static int n = 0;
    printf("i_union_4_state_65 %d\n", n);
    o[0].aval = 0xffffffffU << n++;
    o[1].aval = -1;
    o[2].aval = 1;
    set_bvals(o, 3);
}

void i_union_4_state_128(svLogicVecVal* o) {
    static int n = 0;
    printf("i_union_4_state_128 %d\n", n);
    o[0].aval = 0xffffffffU << n++;
    o[1].aval = -1;
    o[2].aval = -1;
    o[3].aval = -1;
    set_bvals(o, 4);
}

//======================================================================
// Check exported functions
//======================================================================

#define stop() \
    do { \
        printf(__FILE__ ":%d Bad value\n", __LINE__); \
        abort(); \
    } while (0)

void check_bvals(const svLogicVecVal* v, unsigned n);
void check_bvals(const svLogicVecVal* v, unsigned n) {
    for (unsigned i = 0; i < n; i++) {
        if (v[i].bval != 0) {
            printf(__FILE__ ":%d Bad svLogicVecVal bval\n", __LINE__);
            abort();
        }
    }
}

void check_exports() {
    static unsigned n = 0;

    char x_byte;
    unsigned char x_byte_unsigned;
    short x_shortint;
    unsigned short x_shortint_unsigned;
    int x_int;
    unsigned x_int_unsigned;
    sv_longint_t x_longint;
    sv_longint_unsigned_t x_longint_unsigned;
#ifndef NO_TIME
    svLogicVecVal x_time[2];
#endif
#ifndef NO_INTEGER
    svLogicVecVal x_integer[1];
#endif
    double x_real;
#ifndef NO_SHORTREAL
    float x_shortreal;
#endif
    void* x_chandle;
    const char* x_string;
    svBit x_bit;
    svLogic x_logic;

    char x_byte_t;
    unsigned char x_byte_unsigned_t;
    short x_shortint_t;
    unsigned short x_shortint_unsigned_t;
    int x_int_t;
    unsigned x_int_unsigned_t;
    sv_longint_t x_longint_t;
    sv_longint_unsigned_t x_longint_unsigned_t;
#ifndef NO_TIME
    svLogicVecVal x_time_t[2];
#endif
#ifndef NO_INTEGER
    svLogicVecVal x_integer_t[1];
#endif
    double x_real_t;
#ifndef NO_SHORTREAL
    float x_shortreal_t;
#endif
    void* x_chandle_t;
    const char* x_string_t;
    svBit x_bit_t;
    svLogic x_logic_t;

    svBitVecVal x_array_2_state_1[1];
    svBitVecVal x_array_2_state_32[1];
    svBitVecVal x_array_2_state_33[2];
    svBitVecVal x_array_2_state_64[2];
    svBitVecVal x_array_2_state_65[3];
    svBitVecVal x_array_2_state_128[4];

    svBitVecVal x_struct_2_state_1[1];
    svBitVecVal x_struct_2_state_32[1];
    svBitVecVal x_struct_2_state_33[2];
    svBitVecVal x_struct_2_state_64[2];
    svBitVecVal x_struct_2_state_65[3];
    svBitVecVal x_struct_2_state_128[4];

    svBitVecVal x_union_2_state_1[1];
    svBitVecVal x_union_2_state_32[1];
    svBitVecVal x_union_2_state_33[2];
    svBitVecVal x_union_2_state_64[2];
    svBitVecVal x_union_2_state_65[3];
    svBitVecVal x_union_2_state_128[4];

    svLogicVecVal x_array_4_state_1[1];
    svLogicVecVal x_array_4_state_32[1];
    svLogicVecVal x_array_4_state_33[2];
    svLogicVecVal x_array_4_state_64[2];
    svLogicVecVal x_array_4_state_65[3];
    svLogicVecVal x_array_4_state_128[4];

    svLogicVecVal x_struct_4_state_1[1];
    svLogicVecVal x_struct_4_state_32[1];
    svLogicVecVal x_struct_4_state_33[2];
    svLogicVecVal x_struct_4_state_64[2];
    svLogicVecVal x_struct_4_state_65[3];
    svLogicVecVal x_struct_4_state_128[4];

    svLogicVecVal x_union_4_state_1[1];
    svLogicVecVal x_union_4_state_32[1];
    svLogicVecVal x_union_4_state_33[2];
    svLogicVecVal x_union_4_state_64[2];
    svLogicVecVal x_union_4_state_65[3];
    svLogicVecVal x_union_4_state_128[4];

    // Basic types as per IEEE 1800-2017 35.5.6
    e_byte(&x_byte);
    if (x_byte != 10 + n) stop();

    e_byte_unsigned(&x_byte_unsigned);
    if (x_byte_unsigned != 20 + n) stop();

    e_shortint(&x_shortint);
    if (x_shortint != 30 + n) stop();

    e_shortint_unsigned(&x_shortint_unsigned);
    if (x_shortint_unsigned != 40 + n) stop();

    e_int(&x_int);
    if (x_int != 50 + n) stop();

    e_int_unsigned(&x_int_unsigned);
    if (x_int_unsigned != 60 + n) stop();

    e_longint(&x_longint);
    if (x_longint != 70 + n) stop();

    e_longint_unsigned(&x_longint_unsigned);
    if (x_longint_unsigned != 80 + n) stop();

#ifndef NO_TIME
    e_time(x_time);
    if (x_time[0].aval != 90 + n || x_time[1].aval != 0) stop();
    check_bvals(x_time, 2);
#endif

#ifndef NO_INTEGER
    e_integer(x_integer);
    if (x_integer[0].aval != 100 + n) stop();
    check_bvals(x_integer, 1);
#endif

    e_real(&x_real);
    if (x_real != 1.0 * n + 0.5) stop();

#ifndef NO_SHORTREAL
    e_shortreal(&x_shortreal);
    if (x_shortreal != 1.0f * n + 0.25f) stop();
#endif

    e_chandle(&x_chandle);
    if (x_chandle != NULL) stop();

    e_string(&x_string);
    if ((n % 2) == 0) {
        if (strcmp(x_string, "Hello") != 0) stop();
    } else {
        if (strcmp(x_string, "World") != 0) stop();
    }

    e_bit(&x_bit);
    if (x_bit != (n % 2)) stop();

    e_logic(&x_logic);
    if (x_logic != !(n % 2)) stop();

    // Basic types via tyepdef
    e_byte_t(&x_byte_t);
    if (x_byte_t != 10 + 2 * n) stop();

    e_byte_unsigned_t(&x_byte_unsigned_t);
    if (x_byte_unsigned_t != 20 + 2 * n) stop();

    e_shortint_t(&x_shortint_t);
    if (x_shortint_t != 30 + 2 * n) stop();

    e_shortint_unsigned_t(&x_shortint_unsigned_t);
    if (x_shortint_unsigned_t != 40 + 2 * n) stop();

    e_int_t(&x_int_t);
    if (x_int_t != 50 + 2 * n) stop();

    e_int_unsigned_t(&x_int_unsigned_t);
    if (x_int_unsigned_t != 60 + 2 * n) stop();

    e_longint_t(&x_longint_t);
    if (x_longint_t != 70 + 2 * n) stop();

    e_longint_unsigned_t(&x_longint_unsigned_t);
    if (x_longint_unsigned_t != 80 + 2 * n) stop();

#ifndef NO_TIME
    e_time_t(x_time_t);
    if (x_time_t[0].aval != 90 + 2 * n || x_time_t[1].aval != 0) stop();
    check_bvals(x_time_t, 2);
#endif

#ifndef NO_INTEGER
    e_integer_t(x_integer_t);
    if (x_integer_t[0].aval != 100 + 2 * n) stop();
    check_bvals(x_integer_t, 1);
#endif

    e_real_t(&x_real_t);
    if (x_real_t != 1.0 * (2 * n) + 0.5) stop();

#ifndef NO_SHORTREAL
    e_shortreal_t(&x_shortreal_t);
    if (x_shortreal_t != 1.0f * (2 * n) + 0.25f) stop();
#endif

    e_chandle_t(&x_chandle_t);
    if (x_chandle_t != NULL) stop();

    e_string_t(&x_string_t);
    if ((n % 2) == 0) {
        if (strcmp(x_string_t, "Hello") != 0) stop();
    } else {
        if (strcmp(x_string_t, "World") != 0) stop();
    }

    e_bit_t(&x_bit_t);
    if (x_bit_t != (n % 2)) stop();

    e_logic_t(&x_logic_t);
    if (x_logic_t != !(n % 2)) stop();

    const int m = n == 0 ? 0 : n - 1;

    // 2-state packed arrays
    e_array_2_state_1(x_array_2_state_1);
    if (x_array_2_state_1[0] != (n % 2)) stop();

    e_array_2_state_32(x_array_2_state_32);
    if (x_array_2_state_32[0] != 0xffffffff >> n) stop();

    e_array_2_state_33(x_array_2_state_33);
    if (x_array_2_state_33[1] != 1 >> n) stop();
    if (x_array_2_state_33[0] != 0xffffffff >> m) stop();

    e_array_2_state_64(x_array_2_state_64);
    if (x_array_2_state_64[1] != 0xffffffff >> n) stop();
    if (x_array_2_state_64[0] != 0xffffffff) stop();

    e_array_2_state_65(x_array_2_state_65);
    if (x_array_2_state_65[2] != 1 >> n) stop();
    if (x_array_2_state_65[1] != 0xffffffff >> m) stop();
    if (x_array_2_state_65[0] != 0xffffffff) stop();

    e_array_2_state_128(x_array_2_state_128);
    if (x_array_2_state_128[3] != 0xffffffff >> n) stop();
    if (x_array_2_state_128[2] != 0xffffffff) stop();
    if (x_array_2_state_128[1] != 0xffffffff) stop();
    if (x_array_2_state_64[0] != 0xffffffff) stop();

    // 2-state packed structures
    e_struct_2_state_1(x_struct_2_state_1);
    if (x_struct_2_state_1[0] != (n % 2)) stop();

    e_struct_2_state_32(x_struct_2_state_32);
    if (x_struct_2_state_32[0] != 0xffffffff >> n) stop();

    e_struct_2_state_33(x_struct_2_state_33);
    if (x_struct_2_state_33[1] != 1 >> n) stop();
    if (x_struct_2_state_33[0] != 0xffffffff >> m) stop();

    e_struct_2_state_64(x_struct_2_state_64);
    if (x_struct_2_state_64[1] != 0xffffffff >> n) stop();
    if (x_struct_2_state_64[0] != 0xffffffff) stop();

    e_struct_2_state_65(x_struct_2_state_65);
    if (x_struct_2_state_65[2] != 1 >> n) stop();
    if (x_struct_2_state_65[1] != 0xffffffff >> m) stop();
    if (x_struct_2_state_65[0] != 0xffffffff) stop();

    e_struct_2_state_128(x_struct_2_state_128);
    if (x_struct_2_state_128[3] != 0xffffffff >> n) stop();
    if (x_struct_2_state_128[2] != 0xffffffff) stop();
    if (x_struct_2_state_128[1] != 0xffffffff) stop();
    if (x_struct_2_state_64[0] != 0xffffffff) stop();

    // 2-state packed unions
    e_union_2_state_1(x_union_2_state_1);
    if (x_union_2_state_1[0] != (n % 2)) stop();

    e_union_2_state_32(x_union_2_state_32);
    if (x_union_2_state_32[0] != 0xffffffff >> n) stop();

    e_union_2_state_33(x_union_2_state_33);
    if (x_union_2_state_33[1] != 1 >> n) stop();
    if (x_union_2_state_33[0] != 0xffffffff >> m) stop();

    e_union_2_state_64(x_union_2_state_64);
    if (x_union_2_state_64[1] != 0xffffffff >> n) stop();
    if (x_union_2_state_64[0] != 0xffffffff) stop();

    e_union_2_state_65(x_union_2_state_65);
    if (x_union_2_state_65[2] != 1 >> n) stop();
    if (x_union_2_state_65[1] != 0xffffffff >> m) stop();
    if (x_union_2_state_65[0] != 0xffffffff) stop();

    e_union_2_state_128(x_union_2_state_128);
    if (x_union_2_state_128[3] != 0xffffffff >> n) stop();
    if (x_union_2_state_128[2] != 0xffffffff) stop();
    if (x_union_2_state_128[1] != 0xffffffff) stop();
    if (x_union_2_state_64[0] != 0xffffffff) stop();

    // 4-state packed arrays
    e_array_4_state_1(x_array_4_state_1);
    if (x_array_4_state_1[0].aval != (n % 2)) stop();

    e_array_4_state_32(x_array_4_state_32);
    if (x_array_4_state_32[0].aval != 0xffffffff >> n) stop();

    e_array_4_state_33(x_array_4_state_33);
    if (x_array_4_state_33[1].aval != 1 >> n) stop();
    if (x_array_4_state_33[0].aval != 0xffffffff >> m) stop();

    e_array_4_state_64(x_array_4_state_64);
    if (x_array_4_state_64[1].aval != 0xffffffff >> n) stop();
    if (x_array_4_state_64[0].aval != 0xffffffff) stop();

    e_array_4_state_65(x_array_4_state_65);
    if (x_array_4_state_65[2].aval != 1 >> n) stop();
    if (x_array_4_state_65[1].aval != 0xffffffff >> m) stop();
    if (x_array_4_state_65[0].aval != 0xffffffff) stop();

    e_array_4_state_128(x_array_4_state_128);
    if (x_array_4_state_128[3].aval != 0xffffffff >> n) stop();
    if (x_array_4_state_128[2].aval != 0xffffffff) stop();
    if (x_array_4_state_128[1].aval != 0xffffffff) stop();
    if (x_array_4_state_64[0].aval != 0xffffffff) stop();

    check_bvals(x_array_4_state_1, 1);
    check_bvals(x_array_4_state_32, 1);
    check_bvals(x_array_4_state_33, 2);
    check_bvals(x_array_4_state_64, 2);
    check_bvals(x_array_4_state_65, 3);
    check_bvals(x_array_4_state_128, 4);

    // 4-state packed structures
    e_struct_4_state_1(x_struct_4_state_1);
    if (x_struct_4_state_1[0].aval != (n % 2)) stop();

    e_struct_4_state_32(x_struct_4_state_32);
    if (x_struct_4_state_32[0].aval != 0xffffffff >> n) stop();

    e_struct_4_state_33(x_struct_4_state_33);
    if (x_struct_4_state_33[1].aval != 1 >> n) stop();
    if (x_struct_4_state_33[0].aval != 0xffffffff >> m) stop();

    e_struct_4_state_64(x_struct_4_state_64);
    if (x_struct_4_state_64[1].aval != 0xffffffff >> n) stop();
    if (x_struct_4_state_64[0].aval != 0xffffffff) stop();

    e_struct_4_state_65(x_struct_4_state_65);
    if (x_struct_4_state_65[2].aval != 1 >> n) stop();
    if (x_struct_4_state_65[1].aval != 0xffffffff >> m) stop();
    if (x_struct_4_state_65[0].aval != 0xffffffff) stop();

    e_struct_4_state_128(x_struct_4_state_128);
    if (x_struct_4_state_128[3].aval != 0xffffffff >> n) stop();
    if (x_struct_4_state_128[2].aval != 0xffffffff) stop();
    if (x_struct_4_state_128[1].aval != 0xffffffff) stop();
    if (x_struct_4_state_64[0].aval != 0xffffffff) stop();

    check_bvals(x_struct_4_state_1, 1);
    check_bvals(x_struct_4_state_32, 1);
    check_bvals(x_struct_4_state_33, 2);
    check_bvals(x_struct_4_state_64, 2);
    check_bvals(x_struct_4_state_65, 3);
    check_bvals(x_struct_4_state_128, 4);

    // 4-state packed unions
    e_union_4_state_1(x_union_4_state_1);
    if (x_union_4_state_1[0].aval != (n % 2)) stop();

    e_union_4_state_32(x_union_4_state_32);
    if (x_union_4_state_32[0].aval != 0xffffffff >> n) stop();

    e_union_4_state_33(x_union_4_state_33);
    if (x_union_4_state_33[1].aval != 1 >> n) stop();
    if (x_union_4_state_33[0].aval != 0xffffffff >> m) stop();

    e_union_4_state_64(x_union_4_state_64);
    if (x_union_4_state_64[1].aval != 0xffffffff >> n) stop();
    if (x_union_4_state_64[0].aval != 0xffffffff) stop();

    e_union_4_state_65(x_union_4_state_65);
    if (x_union_4_state_65[2].aval != 1 >> n) stop();
    if (x_union_4_state_65[1].aval != 0xffffffff >> m) stop();
    if (x_union_4_state_65[0].aval != 0xffffffff) stop();

    e_union_4_state_128(x_union_4_state_128);
    if (x_union_4_state_128[3].aval != 0xffffffff >> n) stop();
    if (x_union_4_state_128[2].aval != 0xffffffff) stop();
    if (x_union_4_state_128[1].aval != 0xffffffff) stop();
    if (x_union_4_state_64[0].aval != 0xffffffff) stop();

    check_bvals(x_union_4_state_1, 1);
    check_bvals(x_union_4_state_32, 1);
    check_bvals(x_union_4_state_33, 2);
    check_bvals(x_union_4_state_64, 2);
    check_bvals(x_union_4_state_65, 3);
    check_bvals(x_union_4_state_128, 4);

    n++;
}
