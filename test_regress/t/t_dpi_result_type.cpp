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

#include "svdpi.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>

// clang-format off
#if defined(VERILATOR)  // Verilator
# include "Vt_dpi_result_type__Dpi.h"
typedef long long sv_longint_t;
typedef unsigned long long sv_longint_unsigned_t;
# define NO_SHORTREAL
#elif defined(VCS)  // VCS
# include "../vc_hdrs.h"
typedef long long sv_longint_t;
typedef unsigned long long sv_longint_unsigned_t;
# define NO_REAL_EXPORT
#elif defined(NCSC)  // NC
# include "dpi-exp.h"
# include "dpi-imp.h"
typedef long long sv_longint_t;
typedef unsigned long long sv_longint_unsigned_t;
# define NO_STRUCT_OR_UNION
# define NO_SHORTREAL
#elif defined(MS)  // ModelSim
# include "dpi.h"
typedef int64_t sv_longint_t;
typedef uint64_t sv_longint_unsigned_t;
# define NO_STRUCT_OR_UNION
# define NO_ARRAY
#else
# error "Unknown simulator for DPI test"
#endif
// clang-format on

//======================================================================
// Implementations of imported functions
//======================================================================

// Basic types as per IEEE 1800-2017 35.5.5
void i_void() {
    static int n = 0;
    printf("i_void %d\n", n);
    n++;
}

char i_byte() {
    static int n = 0;
    return 10 - n++;
}

unsigned char i_byte_unsigned() {
    static int n = 0;
    return 20 - n++;
}

short i_shortint() {
    static int n = 0;
    return 30 - n++;
}

unsigned short i_shortint_unsigned() {
    static int n = 0;
    return 40 - n++;
}

int i_int() {
    static int n = 0;
    return 50 - n++;
}

unsigned i_int_unsigned() {
    static int n = 0;
    return 60 - n++;
}

sv_longint_t i_longint() {
    static int n = 0;
    return 70 - n++;
}

sv_longint_unsigned_t i_longint_unsigned() {
    static int n = 0;
    return 80 - n++;
}

double i_real() {
    static int n = 0;
    return (-2.0 * n++ - 1.0) / 2.0;
}

#ifndef NO_SHORTREAL
float i_shortreal() {
    static int n = 0;
    return (-4.0f * n++ - 1.0f) / 4.0f;
}
#endif

void* i_chandle() {
    static int n = 0;
    printf("i_chandle %d\n", n);
    return (n++ % 2) ? reinterpret_cast<void*>(&i_chandle) : NULL;
}

const char* i_string() {
    static int n = 0;
    printf("i_string %d\n", n);
    return (n++ % 2) ? "Hello" : "World";
}

svBit i_bit() {
    static int n = 0;
    printf("i_bit %d\n", n);
    return !(n++ % 2);
}

svLogic i_logic() {
    static int n = 0;
    printf("i_logic %d\n", n);
    return n++ % 2;
}

// Basic types via typedefs
char i_byte_t() {
    static int n = 0;
    const char r = 10 - n;
    n += 2;
    return r;
}

unsigned char i_byte_unsigned_t() {
    static int n = 0;
    const unsigned char r = 20 - n;
    n += 2;
    return r;
}

short i_shortint_t() {
    static int n = 0;
    const short r = 30 - n;
    n += 2;
    return r;
}

unsigned short i_shortint_unsigned_t() {
    static int n = 0;
    const unsigned short r = 40 - n;
    n += 2;
    return r;
}

int i_int_t() {
    static int n = 0;
    const int r = 50 - n;
    n += 2;
    return r;
}

unsigned i_int_unsigned_t() {
    static int n = 0;
    const unsigned r = 60 - n;
    n += 2;
    return r;
}

sv_longint_t i_longint_t() {
    static int n = 0;
    const sv_longint_t r = 70 - n;
    n += 2;
    return r;
}

sv_longint_unsigned_t i_longint_unsigned_t() {
    static int n = 0;
    const sv_longint_unsigned_t r = 80 - n;
    n += 2;
    return r;
}

double i_real_t() {
    static int n = 0;
    const double r = (-2.0 * n - 1.0) / 2.0;
    n += 2;
    return r;
}

#ifndef NO_SHORTREAL
float i_shortreal_t() {
    static int n = 0;
    const float r = (-4.0f * n - 1.0f) / 4.0f;
    n += 2;
    return r;
}
#endif

void* i_chandle_t() {
    static int n = 0;
    printf("i_chandle_t %d\n", n);
    return (n++ % 2) ? reinterpret_cast<void*>(&i_chandle) : NULL;
}

const char* i_string_t() {
    static int n = 0;
    printf("i_string_t %d\n", n);
    return (n++ % 2) ? "Hello" : "World";
}

svBit i_bit_t() {
    static int n = 0;
    printf("i_bit_t %d\n", n);
    return !(n++ % 2);
}

svLogic i_logic_t() {
    static int n = 0;
    printf("i_logic_t %d\n", n);
    return n++ % 2;
}

#ifndef NO_ARRAY
// 2-state packed arrays of width <= 32
svBitVecVal i_array_2_state_1() {
    static int n = 0;
    printf("i_array_2_state_1 %d\n", n);
    return !(n++ % 2);
}

svBitVecVal i_array_2_state_32() {
    static int n = 0;
    printf("i_array_2_state_32 %d\n", n);
    return 0xffffffffU << n++;
}
#endif

#ifndef NO_STRUCT_OR_UNION
// 2-state packed structures of width <= 32
svBitVecVal i_struct_2_state_1() {
    static int n = 0;
    printf("i_struct_2_state_1 %d\n", n);
    return !(n++ % 2);
}

svBitVecVal i_struct_2_state_32() {
    static int n = 0;
    printf("i_struct_2_state_32 %d\n", n);
    return 0xffffffffU << n++;
}

// 2-state packed unions of width <= 32
svBitVecVal i_union_2_state_1() {
    static int n = 0;
    printf("i_union_2_state_1 %d\n", n);
    return !(n++ % 2);
}

svBitVecVal i_union_2_state_32() {
    static int n = 0;
    printf("i_union_2_state_32 %d\n", n);
    return 0xffffffffU << n++;
}
#endif

//======================================================================
// Check exported functions
//======================================================================

#define stop() \
    do { \
        printf(__FILE__ ":%d Bad value\n", __LINE__); \
        abort(); \
    } while (0)

void check_exports() {
    static int n = 0;

    e_void();

    // Basic types as per IEEE 1800-2017 35.5.5
    if (e_byte() != 10 + n) stop();
    if (e_byte_unsigned() != 20 + n) stop();
    if (e_shortint() != 30 + n) stop();
    if (e_shortint_unsigned() != 40 + n) stop();
    if (e_int() != 50 + n) stop();
    if (e_int_unsigned() != 60 + n) stop();
    if (e_longint() != 70 + n) stop();
    if (e_longint_unsigned() != 80 + n) stop();
#ifndef NO_REAL_EXPORT
    if (e_real() != 1.0 * n + 0.5) stop();
#endif
#ifndef NO_SHORTREAL
    if (e_shortreal() != 1.0f * n + 0.25f) stop();
#endif
    if (e_chandle()) stop();
    if ((n % 2) == 0) {
        if (strcmp(e_string(), "Hello") != 0) stop();
    } else {
        if (strcmp(e_string(), "World") != 0) stop();
    }
    if (e_bit() != (n % 2)) stop();
    if (e_logic() != !(n % 2)) stop();

    // Basic types via tyepdef
    if (e_byte_t() != 10 + 2 * n) stop();
    if (e_byte_unsigned_t() != 20 + 2 * n) stop();
    if (e_shortint_t() != 30 + 2 * n) stop();
    if (e_shortint_unsigned_t() != 40 + 2 * n) stop();
    if (e_int_t() != 50 + 2 * n) stop();
    if (e_int_unsigned_t() != 60 + 2 * n) stop();
    if (e_longint_t() != 70 + 2 * n) stop();
    if (e_longint_unsigned_t() != 80 + 2 * n) stop();
#ifndef NO_REAL_EXPORT
    if (e_real_t() != 1.0 * (2 * n) + 0.5) stop();
#endif
#ifndef NO_SHORTREAL
    if (e_shortreal_t() != 1.0f * (2 * n) + 0.25f) stop();
#endif
    if (e_chandle_t()) stop();
    if ((n % 2) == 0) {
        if (strcmp(e_string_t(), "Hello") != 0) stop();
    } else {
        if (strcmp(e_string_t(), "World") != 0) stop();
    }
    if (e_bit_t() != (n % 2)) stop();
    if (e_logic_t() != !(n % 2)) stop();

#ifndef NO_ARRAY
    // 2-state packed arrays of width <= 32
    if (e_array_2_state_1() != (n % 2)) stop();
    if (e_array_2_state_32() != 0xffffffff >> n) stop();
#endif

#ifndef NO_STRUCT_OR_UNION
    // 2-state packed structures of width <= 32
    if (e_struct_2_state_1() != (n % 2)) stop();
    if (e_struct_2_state_32() != 0xffffffff >> n) stop();

    // 2-state packed unions of width <= 32
    if (e_union_2_state_1() != (n % 2)) stop();
    if (e_union_2_state_32() != 0xffffffff >> n) stop();
#endif

    n++;
}
