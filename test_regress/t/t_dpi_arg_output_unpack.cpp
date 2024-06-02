// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2020 by Yutetsu TAKATSUKASA. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <vector>

// clang-format off
#if defined(NCSC)
// Used by NC's svdpi.h to pick up svLogicVecVal with _.aval and _.bval fields,
// rather than the IEEE 1800-2005 version which has _.a and _.b fields.
# define DPI_COMPATIBILITY_VERSION_1800v2012
#endif

#include "svdpi.h"

#if defined(VERILATOR)  // Verilator
# include "Vt_dpi_arg_output_unpack__Dpi.h"
typedef long long sv_longint_t;
typedef unsigned long long sv_longint_unsigned_t;
# define NO_SHORTREAL
# define NO_UNPACK_STRUCT
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

namespace {  // unnamed namespace

const bool VERBOSE_MESSAGE = false;

#define stop() \
    do { \
        printf(__FILE__ ":%d Bad value\n", __LINE__); \
        abort(); \
    } while (0)

void set_uint(svLogicVecVal* v0, sv_longint_unsigned_t val, int bitwidth) {
    for (int i = 0; i < bitwidth; ++i) {
        if (i < 64)
            svPutBitselLogic(v0, i, (val >> i) & 1);
        else
            svPutBitselLogic(v0, i, 0);
    }
}

void set_uint(svBitVecVal* v0, sv_longint_unsigned_t val, int bitwidth) {
    for (int i = 0; i < bitwidth; ++i) {
        if (i < 64)
            svPutBitselBit(v0, i, (val >> i) & 1);
        else
            svPutBitselBit(v0, i, 0);
    }
}

template <typename T>
void set_0d(T* v) {
    *v = 42;
}
template <typename T>
void set_1d(T* v) {
    v[0] = 43;
    v[1] = 44;
}

template <typename T>
void set_2d(T* v) {
    v[0 * 2 + 1] = 45;
    v[1 * 2 + 1] = 46;
    v[2 * 2 + 1] = 47;
}
template <typename T>
void set_3d(T* v) {
    v[(0 * 3 + 0) * 2 + 0] = 48;
    v[(1 * 3 + 0) * 2 + 0] = 49;
    v[(2 * 3 + 0) * 2 + 0] = 50;
    v[(3 * 3 + 0) * 2 + 0] = 51;
}

void set_0d(svLogicVecVal* v, int bitwidth) { set_uint(v, 42, bitwidth); }

void set_1d(svLogicVecVal* v, int bitwidth) {
    const int unit = (bitwidth + 31) / 32;
    set_uint(v + 0 * unit, 43, bitwidth);
    set_uint(v + 1 * unit, 44, bitwidth);
}

void set_2d(svLogicVecVal* v, int bitwidth) {
    const int unit = (bitwidth + 31) / 32;
    set_uint(v + (0 * 2 + 1) * unit, 45, bitwidth);
    set_uint(v + (1 * 2 + 1) * unit, 46, bitwidth);
    set_uint(v + (2 * 2 + 1) * unit, 47, bitwidth);
}

void set_3d(svLogicVecVal* v, int bitwidth) {
    const int unit = (bitwidth + 31) / 32;
    set_uint(v + ((0 * 3 + 0) * 2 + 0) * unit, 48, bitwidth);
    set_uint(v + ((1 * 3 + 0) * 2 + 0) * unit, 49, bitwidth);
    set_uint(v + ((2 * 3 + 0) * 2 + 0) * unit, 50, bitwidth);
    set_uint(v + ((3 * 3 + 0) * 2 + 0) * unit, 51, bitwidth);
}

void set_0d_scalar(svScalar* v) { *v = sv_0; }

void set_1d_scalar(svScalar* v) {
    v[0] = sv_1;
    v[1] = sv_0;
}

void set_2d_scalar(svScalar* v) {
    v[0 * 2 + 1] = sv_1;
    v[1 * 2 + 1] = sv_0;
    v[2 * 2 + 1] = sv_1;
}

void set_3d_scalar(svScalar* v) {
    v[(0 * 3 + 0) * 2 + 0] = sv_0;
    v[(1 * 3 + 0) * 2 + 0] = sv_1;
    v[(2 * 3 + 0) * 2 + 0] = sv_0;
    v[(3 * 3 + 0) * 2 + 0] = sv_1;
}

void set_0d(svBitVecVal* v, int bitwidth) { set_uint(v, 42, bitwidth); }

void set_1d(svBitVecVal* v, int bitwidth) {
    const int unit = (bitwidth + 31) / 32;
    set_uint(v + 0 * unit, 43, bitwidth);
    set_uint(v + 1 * unit, 44, bitwidth);
}

void set_2d(svBitVecVal* v, int bitwidth) {
    const int unit = (bitwidth + 31) / 32;
    set_uint(v + (0 * 2 + 1) * unit, 45, bitwidth);
    set_uint(v + (1 * 2 + 1) * unit, 46, bitwidth);
    set_uint(v + (2 * 2 + 1) * unit, 47, bitwidth);
}

void set_3d(svBitVecVal* v, int bitwidth) {
    const int unit = (bitwidth + 31) / 32;
    set_uint(v + ((0 * 3 + 0) * 2 + 0) * unit, 48, bitwidth);
    set_uint(v + ((1 * 3 + 0) * 2 + 0) * unit, 49, bitwidth);
    set_uint(v + ((2 * 3 + 0) * 2 + 0) * unit, 50, bitwidth);
    set_uint(v + ((3 * 3 + 0) * 2 + 0) * unit, 51, bitwidth);
}

template <typename T>
bool compare(const T& act, const T& exp) {
    if (exp == act) {
        if (VERBOSE_MESSAGE) std::cout << "OK Exp:" << exp << " actual:" << act << std::endl;
        return true;
    } else {
        std::cout << "NG Exp:" << exp << " actual:" << act << std::endl;
        return false;
    }
}

template <typename T>
bool check_0d(T v) {
    return compare<T>(v, 42);
}
template <typename T>
bool check_1d(const T (&v)[2]) {
    return compare<T>(v[0], 43) && compare<T>(v[1], 44);
}
template <typename T>
bool check_2d(const T (&v)[3][2]) {
    return compare<T>(v[0][1], 45) && compare<T>(v[1][1], 46) && compare<T>(v[2][1], 47);
}
template <typename T>
bool check_3d(const T (&v)[4][3][2]) {
    return compare<T>(v[0][0][0], 48) && compare<T>(v[1][0][0], 49) && compare<T>(v[2][0][0], 50)
           && compare<T>(v[3][0][0], 51);
}

bool compare(const svLogicVecVal* v0, sv_longint_unsigned_t val, int bitwidth) {
    for (int i = 0; i < bitwidth; ++i) {
        const bool act_bit = svGetBitselLogic(v0, i);
        const bool exp_bit = (i < 64) ? ((val >> i) & 1) : false;
        if (act_bit != exp_bit) {
            std::cout << "Mismatch at bit:" << i << " exp:" << exp_bit << " act:" << act_bit;
            return false;
        }
    }
    if (VERBOSE_MESSAGE) {
        std::cout << "OK " << val << " as expected (width:" << bitwidth << ")" << std::endl;
    }
    return true;
}

bool compare(const svBitVecVal* v0, sv_longint_unsigned_t val, int bitwidth) {
    for (int i = 0; i < bitwidth; ++i) {
        const bool act_bit = svGetBitselBit(v0, i);
        const bool exp_bit = (i < 64) ? ((val >> i) & 1) : false;
        if (act_bit != exp_bit) {
            std::cout << "Mismatch at bit:" << i << " exp:" << exp_bit << " act:" << act_bit;
            return false;
        }
    }
    if (VERBOSE_MESSAGE) {
        std::cout << "OK " << val << " as expected (width:" << bitwidth << ")" << std::endl;
    }
    return true;
}

template <typename T, size_t N>
bool check_0d(const T (&v)[N], int bitwidth) {
    return compare(v, 42, bitwidth);
}
template <typename T, size_t N>
bool check_1d(const T (&v)[2][N], int bitwidth) {
    return compare(v[0], 43, bitwidth) && compare(v[1], 44, bitwidth);
}
template <typename T, size_t N>
bool check_2d(const T (&v)[3][2][N], int bitwidth) {
    return compare(v[0][1], 45, bitwidth) && compare(v[1][1], 46, bitwidth)
           && compare(v[2][1], 47, bitwidth);
}
template <typename T, size_t N>
bool check_3d(const T (&v)[4][3][2][N], int bitwidth) {
    return compare(v[0][0][0], 48, bitwidth) && compare(v[1][0][0], 49, bitwidth)
           && compare(v[2][0][0], 50, bitwidth) && compare(v[3][0][0], 51, bitwidth);
}

}  // unnamed namespace

void* get_non_null() {
    static int v;
    return &v;
}

void i_byte_0d(char* v) { set_0d(v); }
void i_byte_1d(char* v) { set_1d(v); }
void i_byte_2d(char* v) { set_2d(v); }
void i_byte_3d(char* v) { set_3d(v); }

void i_byte_unsigned_0d(unsigned char* v) { set_0d(v); }
void i_byte_unsigned_1d(unsigned char* v) { set_1d(v); }
void i_byte_unsigned_2d(unsigned char* v) { set_2d(v); }
void i_byte_unsigned_3d(unsigned char* v) { set_3d(v); }

void i_shortint_0d(short* v) { set_0d(v); }
void i_shortint_1d(short* v) { set_1d(v); }
void i_shortint_2d(short* v) { set_2d(v); }
void i_shortint_3d(short* v) { set_3d(v); }

void i_shortint_unsigned_0d(unsigned short* v) { set_0d(v); }
void i_shortint_unsigned_1d(unsigned short* v) { set_1d(v); }
void i_shortint_unsigned_2d(unsigned short* v) { set_2d(v); }
void i_shortint_unsigned_3d(unsigned short* v) { set_3d(v); }

void i_int_0d(int* v) { set_0d(v); }
void i_int_1d(int* v) { set_1d(v); }
void i_int_2d(int* v) { set_2d(v); }
void i_int_3d(int* v) { set_3d(v); }

void i_int_unsigned_0d(unsigned int* v) { set_0d(v); }
void i_int_unsigned_1d(unsigned int* v) { set_1d(v); }
void i_int_unsigned_2d(unsigned int* v) { set_2d(v); }
void i_int_unsigned_3d(unsigned int* v) { set_3d(v); }

void i_longint_0d(sv_longint_t* v) { set_0d(v); }
void i_longint_1d(sv_longint_t* v) { set_1d(v); }
void i_longint_2d(sv_longint_t* v) { set_2d(v); }
void i_longint_3d(sv_longint_t* v) { set_3d(v); }

void i_longint_unsigned_0d(sv_longint_unsigned_t* v) { set_0d(v); }
void i_longint_unsigned_1d(sv_longint_unsigned_t* v) { set_1d(v); }
void i_longint_unsigned_2d(sv_longint_unsigned_t* v) { set_2d(v); }
void i_longint_unsigned_3d(sv_longint_unsigned_t* v) { set_3d(v); }

#ifndef NO_TIME
void i_time_0d(svLogicVecVal* v) { set_0d(v, 64); }
void i_time_1d(svLogicVecVal* v) { set_1d(v, 64); }
void i_time_2d(svLogicVecVal* v) { set_2d(v, 64); }
void i_time_3d(svLogicVecVal* v) { set_3d(v, 64); }
#endif

#ifndef NO_INTEGER
void i_integer_0d(svLogicVecVal* v) { set_0d(v, 32); }
void i_integer_1d(svLogicVecVal* v) { set_1d(v, 32); }
void i_integer_2d(svLogicVecVal* v) { set_2d(v, 32); }
void i_integer_3d(svLogicVecVal* v) { set_3d(v, 32); }
#endif

void i_real_0d(double* v) { set_0d(v); }
void i_real_1d(double* v) { set_1d(v); }
void i_real_2d(double* v) { set_2d(v); }
void i_real_3d(double* v) { set_3d(v); }

#ifndef NO_SHORTREAL
void i_shortreal_0d(float* v) { set_0d(v); }
void i_shortreal_1d(float* v) { set_1d(v); }
void i_shortreal_2d(float* v) { set_2d(v); }
void i_shortreal_3d(float* v) { set_3d(v); }
#endif

void i_chandle_0d(void** v) { v[0] = get_non_null(); }
void i_chandle_1d(void** v) {
    v[0] = get_non_null();
    v[1] = get_non_null();
}
void i_chandle_2d(void** v) {
    v[2 * 0 + 1] = get_non_null();
    v[2 * 1 + 1] = get_non_null();
    v[2 * 2 + 1] = get_non_null();
}
void i_chandle_3d(void** v) {
    v[(0 * 3 + 0) * 2 + 0] = get_non_null();
    v[(1 * 3 + 0) * 2 + 0] = get_non_null();
    v[(2 * 3 + 0) * 2 + 0] = get_non_null();
    v[(3 * 3 + 0) * 2 + 0] = get_non_null();
}

void i_string_0d(const char** v) {
    static const char s[] = "42";
    v[0] = s;
}
void i_string_1d(const char** v) {
    static const char s0[] = "43";
    static const char s1[] = "44";
    v[0] = s0;
    v[1] = s1;
}
void i_string_2d(const char** v) {
    static const char empty[] = "";
    static const char s0[] = "45";
    static const char s1[] = "46";
    static const char s2[] = "47";
    for (int i = 0; i < 3 * 2; ++i) v[i] = empty;
    v[2 * 0 + 1] = s0;
    v[2 * 1 + 1] = s1;
    v[2 * 2 + 1] = s2;
}
void i_string_3d(const char** v) {
    static const char empty[] = "";
    static const char s0[] = "48";
    static const char s1[] = "49";
    static const char s2[] = "50";
    static const char s3[] = "51";
    for (int i = 0; i < 4 * 3 * 2; ++i) v[i] = empty;
    v[(0 * 3 + 0) * 2 + 0] = s0;
    v[(1 * 3 + 0) * 2 + 0] = s1;
    v[(2 * 3 + 0) * 2 + 0] = s2;
    v[(3 * 3 + 0) * 2 + 0] = s3;
}

void i_bit1_0d(svBit* v) { set_0d_scalar(v); }
void i_bit1_1d(svBit* v) { set_1d_scalar(v); }
void i_bit1_2d(svBit* v) { set_2d_scalar(v); }
void i_bit1_3d(svBit* v) { set_3d_scalar(v); }

void i_bit7_0d(svBitVecVal* v) { set_0d(v, 7); }
void i_bit7_1d(svBitVecVal* v) { set_1d(v, 7); }
void i_bit7_2d(svBitVecVal* v) { set_2d(v, 7); }
void i_bit7_3d(svBitVecVal* v) { set_3d(v, 7); }

void i_bit121_0d(svBitVecVal* v) { set_0d(v, 121); }
void i_bit121_1d(svBitVecVal* v) { set_1d(v, 121); }
void i_bit121_2d(svBitVecVal* v) { set_2d(v, 121); }
void i_bit121_3d(svBitVecVal* v) { set_3d(v, 121); }

void i_logic1_0d(svLogic* v) { set_0d_scalar(v); }
void i_logic1_1d(svLogic* v) { set_1d_scalar(v); }
void i_logic1_2d(svLogic* v) { set_2d_scalar(v); }
void i_logic1_3d(svLogic* v) { set_3d_scalar(v); }

void i_logic7_0d(svLogicVecVal* v) { set_0d(v, 7); }
void i_logic7_1d(svLogicVecVal* v) { set_1d(v, 7); }
void i_logic7_2d(svLogicVecVal* v) { set_2d(v, 7); }
void i_logic7_3d(svLogicVecVal* v) { set_3d(v, 7); }

void i_logic121_0d(svLogicVecVal* v) { set_0d(v, 121); }
void i_logic121_1d(svLogicVecVal* v) { set_1d(v, 121); }
void i_logic121_2d(svLogicVecVal* v) { set_2d(v, 121); }
void i_logic121_3d(svLogicVecVal* v) { set_3d(v, 121); }

void i_pack_struct_0d(svLogicVecVal* v) { set_0d(v, 7); }
void i_pack_struct_1d(svLogicVecVal* v) { set_1d(v, 7); }
void i_pack_struct_2d(svLogicVecVal* v) { set_2d(v, 7); }
void i_pack_struct_3d(svLogicVecVal* v) { set_3d(v, 7); }

#ifndef NO_UNPACK_STRUCT
void i_unpack_struct_0d(unpack_struct_t* v) { set_uint(v->val, 42, 121); }
void i_unpack_struct_1d(unpack_struct_t* v) {
    set_uint(v[0].val, 43, 121);
    set_uint(v[1].val, 44, 121);
}
void i_unpack_struct_2d(unpack_struct_t* v) {
    set_uint(v[0 * 2 + 1].val, 45, 121);
    set_uint(v[1 * 2 + 1].val, 46, 121);
    set_uint(v[2 * 2 + 1].val, 47, 121);
}
void i_unpack_struct_3d(unpack_struct_t* v) {
    set_uint(v[(0 * 3 + 0) * 2 + 0].val, 48, 121);
    set_uint(v[(1 * 3 + 0) * 2 + 0].val, 49, 121);
    set_uint(v[(2 * 3 + 0) * 2 + 0].val, 50, 121);
    set_uint(v[(3 * 3 + 0) * 2 + 0].val, 51, 121);
}
#endif

void check_exports() {
    {
        char byte_array[4][3][2];
        e_byte_0d(&byte_array[3][2][1]);
        if (!check_0d(byte_array[3][2][1])) stop();
        e_byte_1d(&byte_array[2][1][0]);
        if (!check_1d(byte_array[2][1])) stop();
        e_byte_2d(&byte_array[1][0][0]);
        if (!check_2d(byte_array[1])) stop();
        e_byte_3d(&byte_array[0][0][0]);
        if (!check_3d(byte_array)) stop();
    }
    {
        unsigned char byte_unsigned_array[4][3][2];
        e_byte_unsigned_0d(&byte_unsigned_array[3][2][1]);
        if (!check_0d(byte_unsigned_array[3][2][1])) stop();
        e_byte_unsigned_1d(&byte_unsigned_array[2][1][0]);
        if (!check_1d(byte_unsigned_array[2][1])) stop();
        e_byte_unsigned_2d(&byte_unsigned_array[1][0][0]);
        if (!check_2d(byte_unsigned_array[1])) stop();
        e_byte_unsigned_3d(&byte_unsigned_array[0][0][0]);
        if (!check_3d(byte_unsigned_array)) stop();
    }
    {
        short shortint_array[4][3][2];
        e_shortint_0d(&shortint_array[3][2][1]);
        if (!check_0d(shortint_array[3][2][1])) stop();
        e_shortint_1d(&shortint_array[2][1][0]);
        if (!check_1d(shortint_array[2][1])) stop();
        e_shortint_2d(&shortint_array[1][0][0]);
        if (!check_2d(shortint_array[1])) stop();
        e_shortint_3d(&shortint_array[0][0][0]);
        if (!check_3d(shortint_array)) stop();
    }
    {
        unsigned short shortint_unsigned_array[4][3][2];
        e_shortint_unsigned_0d(&shortint_unsigned_array[3][2][1]);
        if (!check_0d(shortint_unsigned_array[3][2][1])) stop();
        e_shortint_unsigned_1d(&shortint_unsigned_array[2][1][0]);
        if (!check_1d(shortint_unsigned_array[2][1])) stop();
        e_shortint_unsigned_2d(&shortint_unsigned_array[1][0][0]);
        if (!check_2d(shortint_unsigned_array[1])) stop();
        e_shortint_unsigned_3d(&shortint_unsigned_array[0][0][0]);
        if (!check_3d(shortint_unsigned_array)) stop();
    }

    {
        int int_array[4][3][2];
        e_int_0d(&int_array[3][2][1]);
        if (!check_0d(int_array[3][2][1])) stop();
        e_int_1d(&int_array[2][1][0]);
        if (!check_1d(int_array[2][1])) stop();
        e_int_2d(&int_array[1][0][0]);
        if (!check_2d(int_array[1])) stop();
        e_int_3d(&int_array[0][0][0]);
        if (!check_3d(int_array)) stop();
    }
    {
        unsigned int int_unsigned_array[4][3][2];
        e_int_unsigned_0d(&int_unsigned_array[3][2][1]);
        if (!check_0d(int_unsigned_array[3][2][1])) stop();
        e_int_unsigned_1d(&int_unsigned_array[2][1][0]);
        if (!check_1d(int_unsigned_array[2][1])) stop();
        e_int_unsigned_2d(&int_unsigned_array[1][0][0]);
        if (!check_2d(int_unsigned_array[1])) stop();
        e_int_unsigned_3d(&int_unsigned_array[0][0][0]);
        if (!check_3d(int_unsigned_array)) stop();
    }

    {
        sv_longint_t longint_array[4][3][2];
        e_longint_0d(&longint_array[3][2][1]);
        if (!check_0d(longint_array[3][2][1])) stop();
        e_longint_1d(&longint_array[2][1][0]);
        if (!check_1d(longint_array[2][1])) stop();
        e_longint_2d(&longint_array[1][0][0]);
        if (!check_2d(longint_array[1])) stop();
        e_longint_3d(&longint_array[0][0][0]);
        if (!check_3d(longint_array)) stop();
    }
    {
        sv_longint_unsigned_t longint_unsigned_array[4][3][2];
        e_longint_unsigned_0d(&longint_unsigned_array[3][2][1]);
        if (!check_0d(longint_unsigned_array[3][2][1])) stop();
        e_longint_unsigned_1d(&longint_unsigned_array[2][1][0]);
        if (!check_1d(longint_unsigned_array[2][1])) stop();
        e_longint_unsigned_2d(&longint_unsigned_array[1][0][0]);
        if (!check_2d(longint_unsigned_array[1])) stop();
        e_longint_unsigned_3d(&longint_unsigned_array[0][0][0]);
        if (!check_3d(longint_unsigned_array)) stop();
    }

#ifndef NO_TIME
    {
        svLogicVecVal time_array[4][3][2][2];
        e_time_0d(time_array[3][2][1]);
        if (!check_0d(time_array[3][2][1], 64)) stop();
        e_time_1d(time_array[2][1][0]);
        if (!check_1d(time_array[2][1], 64)) stop();
        e_time_2d(time_array[1][0][0]);
        if (!check_2d(time_array[1], 64)) stop();
        e_time_3d(time_array[0][0][0]);
        if (!check_3d(time_array, 64)) stop();
    }
#endif

#ifndef NO_INTEGER
    {
        svLogicVecVal integer_array[4][3][2][1];
        e_integer_0d(integer_array[3][2][1]);
        if (!check_0d(integer_array[3][2][1], 32)) stop();
        e_integer_1d(integer_array[2][1][0]);
        if (!check_1d(integer_array[2][1], 32)) stop();
        e_integer_2d(integer_array[1][0][0]);
        if (!check_2d(integer_array[1], 32)) stop();
        e_integer_3d(integer_array[0][0][0]);
        if (!check_3d(integer_array, 32)) stop();
    }
#endif

    {
        double real_array[4][3][2];
        e_real_0d(&real_array[3][2][1]);
        if (!check_0d(real_array[3][2][1])) stop();
        e_real_1d(&real_array[2][1][0]);
        if (!check_1d(real_array[2][1])) stop();
        e_real_2d(&real_array[1][0][0]);
        if (!check_2d(real_array[1])) stop();
        e_real_3d(&real_array[0][0][0]);
        if (!check_3d(real_array)) stop();
    }
#ifndef NO_SHORTREAL
    {
        float shortreal_array[4][3][2];
        e_shortreal_0d(&shortreal_array[3][2][1]);
        if (!check_0d(shortreal_array[3][2][1])) stop();
        e_shortreal_1d(&shortreal_array[2][1][0]);
        if (!check_1d(shortreal_array[2][1])) stop();
        e_shortreal_2d(&shortreal_array[1][0][0]);
        if (!check_2d(shortreal_array[1])) stop();
        e_shortreal_3d(&shortreal_array[0][0][0]);
        if (!check_3d(shortreal_array)) stop();
    }
#endif

    {
        void* chandle_array[4][3][2];
        for (int i = 0; i < 4; ++i)
            for (int j = 0; j < 3; ++j)
                for (int k = 0; k < 2; ++k) chandle_array[i][j][k] = NULL;
        e_chandle_0d(&chandle_array[3][2][1]);
        if (!chandle_array[3][2][1]) stop();
        e_chandle_1d(&chandle_array[2][1][0]);
        if (!chandle_array[2][1][0]) stop();
        if (!chandle_array[2][1][1]) stop();
        e_chandle_2d(&chandle_array[1][0][0]);
        if (!chandle_array[1][0][1]) stop();
        if (!chandle_array[1][1][1]) stop();
        if (!chandle_array[1][2][1]) stop();
        e_chandle_3d(&chandle_array[0][0][0]);
        if (!chandle_array[0][0][0]) stop();
        if (!chandle_array[1][0][0]) stop();
        if (!chandle_array[2][0][0]) stop();
        if (!chandle_array[3][0][0]) stop();
    }

    {
        const char* string_array[4][3][2];
        for (int i = 0; i < 4; ++i)
            for (int j = 0; j < 3; ++j)
                for (int k = 0; k < 2; ++k) string_array[i][j][k] = NULL;
        e_string_0d(&string_array[3][2][1]);
        if (!compare<std::string>(string_array[3][2][1], "42")) stop();
        e_string_1d(&string_array[2][1][0]);
        if (!compare<std::string>(string_array[2][1][0], "43")) stop();
        if (!compare<std::string>(string_array[2][1][1], "44")) stop();
        e_string_2d(&string_array[1][0][0]);
        if (!compare<std::string>(string_array[1][0][1], "45")) stop();
        if (!compare<std::string>(string_array[1][1][1], "46")) stop();
        if (!compare<std::string>(string_array[1][2][1], "47")) stop();
        e_string_3d(&string_array[0][0][0]);
        if (!compare<std::string>(string_array[0][0][0], "48")) stop();
        if (!compare<std::string>(string_array[1][0][0], "49")) stop();
        if (!compare<std::string>(string_array[2][0][0], "50")) stop();
        if (!compare<std::string>(string_array[3][0][0], "51")) stop();
    }

    {
        svBitVecVal bit7_array[4][3][2][1];
        e_bit7_0d(bit7_array[3][2][1]);
        if (!check_0d(bit7_array[3][2][1], 7)) stop();
        e_bit7_1d(bit7_array[2][1][0]);
        if (!check_1d(bit7_array[2][1], 7)) stop();
        e_bit7_2d(bit7_array[1][0][0]);
        if (!check_2d(bit7_array[1], 7)) stop();
        e_bit7_3d(bit7_array[0][0][0]);
        if (!check_3d(bit7_array, 7)) stop();
    }

    {
        svBitVecVal bit121_array[4][3][2][4];
        e_bit121_0d(bit121_array[3][2][1]);
        if (!check_0d(bit121_array[3][2][1], 121)) stop();
        e_bit121_1d(bit121_array[2][1][0]);
        if (!check_1d(bit121_array[2][1], 121)) stop();
        e_bit121_2d(bit121_array[1][0][0]);
        if (!check_2d(bit121_array[1], 121)) stop();
        e_bit121_3d(bit121_array[0][0][0]);
        if (!check_3d(bit121_array, 121)) stop();
    }
    {
        svLogicVecVal logic7_array[4][3][2][1];
        e_logic7_0d(logic7_array[3][2][1]);
        if (!check_0d(logic7_array[3][2][1], 7)) stop();
        e_logic7_1d(logic7_array[2][1][0]);
        if (!check_1d(logic7_array[2][1], 7)) stop();
        e_logic7_2d(logic7_array[1][0][0]);
        if (!check_2d(logic7_array[1], 7)) stop();
        e_logic7_3d(logic7_array[0][0][0]);
        if (!check_3d(logic7_array, 7)) stop();
    }

    {
        svLogicVecVal logic121_array[4][3][2][4];
        e_logic121_0d(logic121_array[3][2][1]);
        if (!check_0d(logic121_array[3][2][1], 121)) stop();
        e_logic121_1d(logic121_array[2][1][0]);
        if (!check_1d(logic121_array[2][1], 121)) stop();
        e_logic121_2d(logic121_array[1][0][0]);
        if (!check_2d(logic121_array[1], 121)) stop();
        e_logic121_3d(logic121_array[0][0][0]);
        if (!check_3d(logic121_array, 121)) stop();
    }

    {
        svLogicVecVal pack_struct_array[4][3][2][1];
        e_pack_struct_0d(pack_struct_array[3][2][1]);
        if (!check_0d(pack_struct_array[3][2][1], 7)) stop();
        e_pack_struct_1d(pack_struct_array[2][1][0]);
        if (!check_1d(pack_struct_array[2][1], 7)) stop();
        e_pack_struct_2d(pack_struct_array[1][0][0]);
        if (!check_2d(pack_struct_array[1], 7)) stop();
        e_pack_struct_3d(pack_struct_array[0][0][0]);
        if (!check_3d(pack_struct_array, 7)) stop();
    }

#ifndef NO_UNPACK_STRUCT
    {
        unpack_struct_t unpack_struct_array[4][3][2];
        e_unpack_struct_0d(&unpack_struct_array[3][2][1]);
        if (!compare(unpack_struct_array[3][2][1].val, 42, 121)) stop();
        e_unpack_struct_1d(&unpack_struct_array[2][1][0]);
        if (!compare(unpack_struct_array[2][1][0].val, 43, 121)) stop();
        if (!compare(unpack_struct_array[2][1][1].val, 44, 121)) stop();
        e_unpack_struct_2d(&unpack_struct_array[1][0][0]);
        if (!compare(unpack_struct_array[1][0][1].val, 45, 121)) stop();
        if (!compare(unpack_struct_array[1][1][1].val, 46, 121)) stop();
        if (!compare(unpack_struct_array[1][2][1].val, 47, 121)) stop();
        e_unpack_struct_3d(&unpack_struct_array[0][0][0]);
        if (!compare(unpack_struct_array[0][0][0].val, 48, 121)) stop();
        if (!compare(unpack_struct_array[1][0][0].val, 49, 121)) stop();
        if (!compare(unpack_struct_array[2][0][0].val, 50, 121)) stop();
        if (!compare(unpack_struct_array[3][0][0].val, 51, 121)) stop();
    }
#endif
}
