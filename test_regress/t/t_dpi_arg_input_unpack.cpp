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
# include "Vt_dpi_arg_input_unpack__Dpi.h"
typedef long long sv_longint_t;
typedef unsigned long long sv_longint_unsigned_t;
typedef const void** sv_chandle_array_ptr_t;
# define NO_SHORTREAL
# define NO_UNPACK_STRUCT
# define CONSTARG const
#elif defined(VCS)  // VCS
# include "../vc_hdrs.h"
typedef long long sv_longint_t;
typedef unsigned long long sv_longint_unsigned_t;
typedef void** sv_chandle_array_ptr_t;
# define NO_TIME
# define CONSTARG const
#elif defined(NCSC)  // NC
# include "dpi-exp.h"
# include "dpi-imp.h"
typedef long long sv_longint_t;
typedef unsigned long long sv_longint_unsigned_t;
typedef void** sv_chandle_array_ptr_t;
# define NO_TIME
# define NO_INTEGER
# define NO_SHORTREAL
// Sadly NC does not declare pass-by reference input arguments as const
# define CONSTARG
#elif defined(MS)  // ModelSim
# include "dpi.h"
typedef int64_t sv_longint_t;
typedef uint64_t sv_longint_unsigned_t;
typedef const void** sv_chandle_array_ptr_t;
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

template <typename T>
bool check_0d(T v) {
    return compare<T>(v, 42);
}
template <typename T>
bool check_1d(const T* v) {
    return compare<T>(v[0], 43) && compare<T>(v[1], 44);
}
template <typename T>
bool check_2d(const T* v) {
    return compare<T>(v[0 * 2 + 1], 45) && compare<T>(v[1 * 2 + 1], 46)
           && compare<T>(v[2 * 2 + 1], 47);
}
template <typename T>
bool check_3d(const T* v) {
    return compare<T>(v[(0 * 3 + 0) * 2 + 0], 48) && compare<T>(v[(1 * 3 + 0) * 2 + 0], 49)
           && compare<T>(v[(2 * 3 + 0) * 2 + 0], 50) && compare<T>(v[(3 * 3 + 0) * 2 + 0], 51);
}

bool check_0d(const svLogicVecVal* v, int bitwidth) { return compare(v, 42, bitwidth); }
bool check_1d(const svLogicVecVal* v, int bitwidth) {
    const int unit = (bitwidth + 31) / 32;
    return compare(v + unit * 0, 43, bitwidth) && compare(v + unit * 1, 44, bitwidth);
}
bool check_2d(const svLogicVecVal* v, int bitwidth) {
    const int unit = (bitwidth + 31) / 32;
    return compare(v + unit * (0 * 2 + 1), 45, bitwidth)
           && compare(v + unit * (1 * 2 + 1), 46, bitwidth)
           && compare(v + unit * (2 * 2 + 1), 47, bitwidth);
}
bool check_3d(const svLogicVecVal* v, int bitwidth) {
    const int unit = (bitwidth + 31) / 32;
    return compare(v + unit * ((0 * 3 + 0) * 2 + 0), 48, bitwidth)
           && compare(v + unit * ((1 * 3 + 0) * 2 + 0), 49, bitwidth)
           && compare(v + unit * ((2 * 3 + 0) * 2 + 0), 50, bitwidth)
           && compare(v + unit * ((3 * 3 + 0) * 2 + 0), 51, bitwidth);
}

bool check_0d(const svBitVecVal* v, int bitwidth) { return compare(v, 42, bitwidth); }
bool check_1d(const svBitVecVal* v, int bitwidth) {
    const int unit = (bitwidth + 31) / 32;
    return compare(v + unit * 0, 43, bitwidth) && compare(v + unit * 1, 44, bitwidth);
}
bool check_2d(const svBitVecVal* v, int bitwidth) {
    const int unit = (bitwidth + 31) / 32;
    return compare(v + unit * (0 * 2 + 1), 45, bitwidth)
           && compare(v + unit * (1 * 2 + 1), 46, bitwidth)
           && compare(v + unit * (2 * 2 + 1), 47, bitwidth);
}
bool check_3d(const svBitVecVal* v, int bitwidth) {
    const int unit = (bitwidth + 31) / 32;
    return compare(v + unit * ((0 * 3 + 0) * 2 + 0), 48, bitwidth)
           && compare(v + unit * ((1 * 3 + 0) * 2 + 0), 49, bitwidth)
           && compare(v + unit * ((2 * 3 + 0) * 2 + 0), 50, bitwidth)
           && compare(v + unit * ((3 * 3 + 0) * 2 + 0), 51, bitwidth);
}

bool check_0d(const char* v) { return compare<std::string>(v, "42"); }
bool check_1d(const char** v) {
    return compare<std::string>(v[0], "43") && compare<std::string>(v[1], "44");
}
bool check_2d(const char** v) {
    return compare<std::string>(v[0 * 2 + 1], "45") && compare<std::string>(v[1 * 2 + 1], "46")
           && compare<std::string>(v[2 * 2 + 1], "47");
}
bool check_3d(const char** v) {
    return compare<std::string>(v[(0 * 3 + 0) * 2 + 0], "48")
           && compare<std::string>(v[(1 * 3 + 0) * 2 + 0], "49")
           && compare<std::string>(v[(2 * 3 + 0) * 2 + 0], "50")
           && compare<std::string>(v[(3 * 3 + 0) * 2 + 0], "51");
}

template <typename T>
void set_values(T (&v)[4][3][2]) {
    for (int i = 0; i < 4; ++i)
        for (int j = 0; j < 3; ++j)
            for (int k = 0; k < 2; ++k) v[i][j][k] = 0;
    v[3][2][1] = 42;
    v[2][1][0] = 43;
    v[2][1][1] = 44;
    v[1][0][1] = 45;
    v[1][1][1] = 46;
    v[1][2][1] = 47;
    v[0][0][0] = 48;
    v[1][0][0] = 49;
    v[2][0][0] = 50;
    v[3][0][0] = 51;
}

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

template <size_t N>
void set_values(svLogicVecVal (&v)[4][3][2][N], int bitwidth) {
    for (int i = 0; i < 4; ++i)
        for (int j = 0; j < 3; ++j)
            for (int k = 0; k < 2; ++k) set_uint(v[i][j][k], 0, bitwidth);
    set_uint(v[3][2][1], 42, bitwidth);

    set_uint(v[2][1][0], 43, bitwidth);
    set_uint(v[2][1][1], 44, bitwidth);

    set_uint(v[1][0][1], 45, bitwidth);
    set_uint(v[1][1][1], 46, bitwidth);
    set_uint(v[1][2][1], 47, bitwidth);

    set_uint(v[0][0][0], 48, bitwidth);
    set_uint(v[1][0][0], 49, bitwidth);
    set_uint(v[2][0][0], 50, bitwidth);
    set_uint(v[3][0][0], 51, bitwidth);
}

template <size_t N>
void set_values(svBitVecVal (&v)[4][3][2][N], int bitwidth) {
    for (int i = 0; i < 4; ++i)
        for (int j = 0; j < 3; ++j)
            for (int k = 0; k < 2; ++k) set_uint(v[i][j][k], 0, bitwidth);
    set_uint(v[3][2][1], 42, bitwidth);

    set_uint(v[2][1][0], 43, bitwidth);
    set_uint(v[2][1][1], 44, bitwidth);

    set_uint(v[1][0][1], 45, bitwidth);
    set_uint(v[1][1][1], 46, bitwidth);
    set_uint(v[1][2][1], 47, bitwidth);

    set_uint(v[0][0][0], 48, bitwidth);
    set_uint(v[1][0][0], 49, bitwidth);
    set_uint(v[2][0][0], 50, bitwidth);
    set_uint(v[3][0][0], 51, bitwidth);
}

sv_chandle_array_ptr_t add_const(void** ptr) {
    return static_cast<sv_chandle_array_ptr_t>(static_cast<void*>(ptr));
}

}  // unnamed namespace

void* get_non_null() {
    static int v;
    return &v;
}

void i_byte_0d(char v) {
    if (!check_0d(v)) stop();
}
void i_byte_1d(const char* v) {
    if (!check_1d(v)) stop();
}
void i_byte_2d(const char* v) {
    if (!check_2d(v)) stop();
}
void i_byte_3d(const char* v) {
    if (!check_3d(v)) stop();
}

void i_byte_unsigned_0d(unsigned char v) {
    if (!check_0d(v)) stop();
}
void i_byte_unsigned_1d(const unsigned char* v) {
    if (!check_1d(v)) stop();
}
void i_byte_unsigned_2d(const unsigned char* v) {
    if (!check_2d(v)) stop();
}
void i_byte_unsigned_3d(const unsigned char* v) {
    if (!check_3d(v)) stop();
}

void i_shortint_0d(short v) {
    if (!check_0d(v)) stop();
}
void i_shortint_1d(const short* v) {
    if (!check_1d(v)) stop();
}
void i_shortint_2d(const short* v) {
    if (!check_2d(v)) stop();
}
void i_shortint_3d(const short* v) {
    if (!check_3d(v)) stop();
}

void i_shortint_unsigned_0d(unsigned short v) {
    if (!check_0d(v)) stop();
}
void i_shortint_unsigned_1d(const unsigned short* v) {
    if (!check_1d(v)) stop();
}
void i_shortint_unsigned_2d(const unsigned short* v) {
    if (!check_2d(v)) stop();
}
void i_shortint_unsigned_3d(const unsigned short* v) {
    if (!check_3d(v)) stop();
}

void i_int_0d(int v) {
    if (!check_0d(v)) stop();
}
void i_int_1d(const int* v) {
    if (!check_1d(v)) stop();
}
void i_int_2d(const int* v) {
    if (!check_2d(v)) stop();
}
void i_int_3d(const int* v) {
    if (!check_3d(v)) stop();
}

void i_int_unsigned_0d(unsigned v) {
    if (!check_0d(v)) stop();
}
void i_int_unsigned_1d(const unsigned* v) {
    if (!check_1d(v)) stop();
}
void i_int_unsigned_2d(const unsigned* v) {
    if (!check_2d(v)) stop();
}
void i_int_unsigned_3d(const unsigned* v) {
    if (!check_3d(v)) stop();
}

void i_longint_0d(sv_longint_t v) {
    if (!check_0d(v)) stop();
}
void i_longint_1d(const sv_longint_t* v) {
    if (!check_1d(v)) stop();
}
void i_longint_2d(const sv_longint_t* v) {
    if (!check_2d(v)) stop();
}
void i_longint_3d(const sv_longint_t* v) {
    if (!check_3d(v)) stop();
}

void i_longint_unsigned_0d(sv_longint_unsigned_t v) {
    if (!check_0d(v)) stop();
}
void i_longint_unsigned_1d(const sv_longint_unsigned_t* v) {
    if (!check_1d(v)) stop();
}
void i_longint_unsigned_2d(const sv_longint_unsigned_t* v) {
    if (!check_2d(v)) stop();
}
void i_longint_unsigned_3d(const sv_longint_unsigned_t* v) {
    if (!check_3d(v)) stop();
}

#ifndef NO_TIME
void i_time_0d(CONSTARG svLogicVecVal* v) {
    if (!check_0d(v, 64)) stop();
}
void i_time_1d(CONSTARG svLogicVecVal* v) {
    if (!check_1d(v, 64)) stop();
}
void i_time_2d(CONSTARG svLogicVecVal* v) {
    if (!check_2d(v, 64)) stop();
}
void i_time_3d(CONSTARG svLogicVecVal* v) {
    if (!check_3d(v, 64)) stop();
}
#endif

#ifndef NO_INTEGER
void i_integer_0d(CONSTARG svLogicVecVal* v) {
    if (!check_0d(v, 32)) stop();
}
void i_integer_1d(CONSTARG svLogicVecVal* v) {
    if (!check_1d(v, 32)) stop();
}
void i_integer_2d(CONSTARG svLogicVecVal* v) {
    if (!check_2d(v, 32)) stop();
}
void i_integer_3d(CONSTARG svLogicVecVal* v) {
    if (!check_3d(v, 32)) stop();
}
#endif

void i_real_0d(double v) {
    if (!check_0d(v)) stop();
}
void i_real_1d(CONSTARG double* v) {
    if (!check_1d(v)) stop();
}
void i_real_2d(CONSTARG double* v) {
    if (!check_2d(v)) stop();
}
void i_real_3d(CONSTARG double* v) {
    if (!check_3d(v)) stop();
}

#ifndef NO_SHORTREAL
void i_shortreal_0d(float v) {
    if (!check_0d(v)) stop();
}
void i_shortreal_1d(CONSTARG float* v) {
    if (!check_1d(v)) stop();
}
void i_shortreal_2d(CONSTARG float* v) {
    if (!check_2d(v)) stop();
}
void i_shortreal_3d(CONSTARG float* v) {
    if (!check_3d(v)) stop();
}
#endif

void i_chandle_0d(void* v) {
    if (!v) stop();
}
void i_chandle_1d(sv_chandle_array_ptr_t v) {
    if (!v[0]) stop();
    if (!v[1]) stop();
}
void i_chandle_2d(sv_chandle_array_ptr_t v) {
    if (!v[2 * 0 + 1]) stop();
    if (!v[2 * 1 + 1]) stop();
    if (!v[2 * 2 + 1]) stop();
}
void i_chandle_3d(sv_chandle_array_ptr_t v) {
    if (!v[(0 * 3 + 0) * 2 + 0]) stop();
    if (!v[(1 * 3 + 0) * 2 + 0]) stop();
    if (!v[(2 * 3 + 0) * 2 + 0]) stop();
    if (!v[(3 * 3 + 0) * 2 + 0]) stop();
}

void i_string_0d(CONSTARG char* v) {
    if (!check_0d(v)) stop();
}
void i_string_1d(CONSTARG char** v) {
    if (!check_1d(v)) stop();
}
void i_string_2d(CONSTARG char** v) {
    if (!check_2d(v)) stop();
}
void i_string_3d(CONSTARG char** v) {
    if (!check_3d(v)) stop();
}

void i_bit1_0d(CONSTARG svBit v) {
    if (!compare<svScalar>(v, sv_0)) stop();
}
void i_bit1_1d(CONSTARG svBit* v) {
    if (!compare<svScalar>(v[0], sv_1)) stop();
    if (!compare<svScalar>(v[1], sv_0)) stop();
}
void i_bit1_2d(CONSTARG svBit* v) {
    if (!compare<svScalar>(v[0 * 2 + 1], sv_1)) stop();
    if (!compare<svScalar>(v[1 * 2 + 1], sv_0)) stop();
    if (!compare<svScalar>(v[2 * 2 + 1], sv_1)) stop();
}
void i_bit1_3d(CONSTARG svBit* v) {
    if (!compare<svScalar>(v[(0 * 3 + 0) * 2 + 0], sv_0)) stop();
    if (!compare<svScalar>(v[(1 * 3 + 0) * 2 + 0], sv_1)) stop();
    if (!compare<svScalar>(v[(2 * 3 + 0) * 2 + 0], sv_0)) stop();
    if (!compare<svScalar>(v[(3 * 3 + 0) * 2 + 0], sv_1)) stop();
}

void i_bit7_0d(CONSTARG svBitVecVal* v) {
    if (!check_0d(v, 7)) stop();
}
void i_bit7_1d(CONSTARG svBitVecVal* v) {
    if (!check_1d(v, 7)) stop();
}
void i_bit7_2d(CONSTARG svBitVecVal* v) {
    if (!check_2d(v, 7)) stop();
}
void i_bit7_3d(CONSTARG svBitVecVal* v) {
    if (!check_3d(v, 7)) stop();
}

void i_bit121_0d(CONSTARG svBitVecVal* v) {
    if (!check_0d(v, 121)) stop();
}
void i_bit121_1d(CONSTARG svBitVecVal* v) {
    if (!check_1d(v, 121)) stop();
}
void i_bit121_2d(CONSTARG svBitVecVal* v) {
    if (!check_2d(v, 121)) stop();
}
void i_bit121_3d(CONSTARG svBitVecVal* v) {
    if (!check_3d(v, 121)) stop();
}

void i_logic1_0d(CONSTARG svLogic v) {
    if (!compare<svScalar>(v, sv_0)) stop();
}
void i_logic1_1d(CONSTARG svLogic* v) {
    if (!compare<svScalar>(v[0], sv_1)) stop();
    if (!compare<svScalar>(v[1], sv_0)) stop();
}
void i_logic1_2d(CONSTARG svLogic* v) {
    if (!compare<svScalar>(v[0 * 2 + 1], sv_1)) stop();
    if (!compare<svScalar>(v[1 * 2 + 1], sv_0)) stop();
    if (!compare<svScalar>(v[2 * 2 + 1], sv_1)) stop();
}
void i_logic1_3d(CONSTARG svLogic* v) {
    if (!compare<svScalar>(v[(0 * 3 + 0) * 2 + 0], sv_0)) stop();
    if (!compare<svScalar>(v[(1 * 3 + 0) * 2 + 0], sv_1)) stop();
    if (!compare<svScalar>(v[(2 * 3 + 0) * 2 + 0], sv_0)) stop();
    if (!compare<svScalar>(v[(3 * 3 + 0) * 2 + 0], sv_1)) stop();
}

void i_logic7_0d(CONSTARG svLogicVecVal* v) {
    if (!check_0d(v, 7)) stop();
}
void i_logic7_1d(CONSTARG svLogicVecVal* v) {
    if (!check_1d(v, 7)) stop();
}
void i_logic7_2d(CONSTARG svLogicVecVal* v) {
    if (!check_2d(v, 7)) stop();
}
void i_logic7_3d(CONSTARG svLogicVecVal* v) {
    if (!check_3d(v, 7)) stop();
}

void i_logic121_0d(CONSTARG svLogicVecVal* v) {
    if (!check_0d(v, 121)) stop();
}
void i_logic121_1d(CONSTARG svLogicVecVal* v) {
    if (!check_1d(v, 121)) stop();
}
void i_logic121_2d(CONSTARG svLogicVecVal* v) {
    if (!check_2d(v, 121)) stop();
}
void i_logic121_3d(CONSTARG svLogicVecVal* v) {
    if (!check_3d(v, 121)) stop();
}

void i_pack_struct_0d(CONSTARG svLogicVecVal* v) {
    if (!check_0d(v, 7)) stop();
}
void i_pack_struct_1d(CONSTARG svLogicVecVal* v) {
    if (!check_1d(v, 7)) stop();
}
void i_pack_struct_2d(CONSTARG svLogicVecVal* v) {
    if (!check_2d(v, 7)) stop();
}
void i_pack_struct_3d(CONSTARG svLogicVecVal* v) {
    if (!check_3d(v, 7)) stop();
}

#ifndef NO_UNPACK_STRUCT
void i_unpack_struct_0d(CONSTARG unpack_struct_t* v) {
    if (!compare(v->val, 42, 121)) stop();
}
void i_unpack_struct_1d(CONSTARG unpack_struct_t* v) {
    if (!compare(v[0].val, 43, 121)) stop();
    if (!compare(v[1].val, 44, 121)) stop();
}
void i_unpack_struct_2d(CONSTARG unpack_struct_t* v) {
    if (!compare(v[0 * 2 + 1].val, 45, 121)) stop();
    if (!compare(v[1 * 2 + 1].val, 46, 121)) stop();
    if (!compare(v[2 * 2 + 1].val, 47, 121)) stop();
}
void i_unpack_struct_3d(CONSTARG unpack_struct_t* v) {
    if (!compare(v[(0 * 3 + 0) * 2 + 0].val, 48, 121)) stop();
    if (!compare(v[(1 * 3 + 0) * 2 + 0].val, 49, 121)) stop();
    if (!compare(v[(2 * 3 + 0) * 2 + 0].val, 50, 121)) stop();
    if (!compare(v[(3 * 3 + 0) * 2 + 0].val, 51, 121)) stop();
}
#endif

void check_exports() {
    {
        char byte_array[4][3][2];
        set_values(byte_array);
        e_byte_0d(byte_array[3][2][1]);
        e_byte_1d(&byte_array[2][1][0]);
        e_byte_2d(&byte_array[1][0][0]);
        e_byte_3d(&byte_array[0][0][0]);
    }
    {
        unsigned char byte_unsigned_array[4][3][2];
        set_values(byte_unsigned_array);
        e_byte_unsigned_0d(byte_unsigned_array[3][2][1]);
        e_byte_unsigned_1d(&byte_unsigned_array[2][1][0]);
        e_byte_unsigned_2d(&byte_unsigned_array[1][0][0]);
        e_byte_unsigned_3d(&byte_unsigned_array[0][0][0]);
    }
    {
        short shortint_array[4][3][2];
        set_values(shortint_array);
        e_shortint_0d(shortint_array[3][2][1]);
        e_shortint_1d(&shortint_array[2][1][0]);
        e_shortint_2d(&shortint_array[1][0][0]);
        e_shortint_3d(&shortint_array[0][0][0]);
    }
    {
        unsigned short shortint_unsigned_array[4][3][2];
        set_values(shortint_unsigned_array);
        e_shortint_unsigned_0d(shortint_unsigned_array[3][2][1]);
        e_shortint_unsigned_1d(&shortint_unsigned_array[2][1][0]);
        e_shortint_unsigned_2d(&shortint_unsigned_array[1][0][0]);
        e_shortint_unsigned_3d(&shortint_unsigned_array[0][0][0]);
    }
    {
        int int_array[4][3][2];
        set_values(int_array);
        e_int_0d(int_array[3][2][1]);
        e_int_1d(&int_array[2][1][0]);
        e_int_2d(&int_array[1][0][0]);
        e_int_3d(&int_array[0][0][0]);
    }
    {
        unsigned int int_unsigned_array[4][3][2];
        set_values(int_unsigned_array);
        e_int_unsigned_0d(int_unsigned_array[3][2][1]);
        e_int_unsigned_1d(&int_unsigned_array[2][1][0]);
        e_int_unsigned_2d(&int_unsigned_array[1][0][0]);
        e_int_unsigned_3d(&int_unsigned_array[0][0][0]);
    }
    {
        sv_longint_t longint_array[4][3][2];
        set_values(longint_array);
        e_longint_0d(longint_array[3][2][1]);
        e_longint_1d(&longint_array[2][1][0]);
        e_longint_2d(&longint_array[1][0][0]);
        e_longint_3d(&longint_array[0][0][0]);
    }
    {
        sv_longint_unsigned_t longint_unsigned_array[4][3][2];
        set_values(longint_unsigned_array);
        e_longint_unsigned_0d(longint_unsigned_array[3][2][1]);
        e_longint_unsigned_1d(&longint_unsigned_array[2][1][0]);
        e_longint_unsigned_2d(&longint_unsigned_array[1][0][0]);
        e_longint_unsigned_3d(&longint_unsigned_array[0][0][0]);
    }
#ifndef NO_TIME
    {
        svLogicVecVal time_array[4][3][2][2];
        set_values(time_array, 64);
        e_time_0d(time_array[3][2][1]);
        e_time_1d(time_array[2][1][0]);
        e_time_2d(&time_array[1][0][0][0]);
        e_time_3d(time_array[0][0][0]);
    }
#endif

#ifndef NO_INTEGER
    {
        svLogicVecVal integer_array[4][3][2][1];
        set_values(integer_array, 32);
        e_integer_0d(integer_array[3][2][1]);
        e_integer_1d(integer_array[2][1][0]);
        e_integer_2d(&integer_array[1][0][0][0]);
        e_integer_3d(integer_array[0][0][0]);
    }
#endif

    {
        double real_array[4][3][2];
        set_values(real_array);
        e_real_0d(real_array[3][2][1]);
        e_real_1d(&real_array[2][1][0]);
        e_real_2d(&real_array[1][0][0]);
        e_real_3d(&real_array[0][0][0]);
    }
#ifndef NO_SHORTREAL
    {
        float shortreal_array[4][3][2];
        set_values(shortreal_array);
        e_shortreal_0d(shortreal_array[3][2][1]);
        e_shortreal_1d(&shortreal_array[2][1][0]);
        e_shortreal_2d(&shortreal_array[1][0][0]);
        e_shortreal_3d(&shortreal_array[0][0][0]);
    }
#endif

    {
        void* chandle_array[4][3][2];
        for (int i = 0; i < 4; ++i)
            for (int j = 0; j < 3; ++j)
                for (int k = 0; k < 2; ++k) chandle_array[i][j][k] = NULL;
        chandle_array[3][2][1] = get_non_null();
        chandle_array[2][1][0] = get_non_null();
        chandle_array[2][1][1] = get_non_null();

        chandle_array[1][0][1] = get_non_null();
        chandle_array[1][1][1] = get_non_null();
        chandle_array[1][2][1] = get_non_null();

        chandle_array[0][0][0] = get_non_null();
        chandle_array[1][0][0] = get_non_null();
        chandle_array[2][0][0] = get_non_null();
        chandle_array[3][0][0] = get_non_null();

        e_chandle_0d(chandle_array[3][2][1]);
        e_chandle_1d(add_const(&chandle_array[2][1][0]));
        e_chandle_2d(add_const(&chandle_array[1][0][0]));
        e_chandle_3d(add_const(&chandle_array[0][0][0]));
    }

    {
        std::vector<char> buf;
        buf.resize(4 * 3 * 2 * 16, '\0');
        buf[((3 * 3 + 2) * 2 + 1) * 16 + 0] = '4';
        buf[((3 * 3 + 2) * 2 + 1) * 16 + 1] = '2';
        buf[((2 * 3 + 1) * 2 + 0) * 16 + 0] = '4';
        buf[((2 * 3 + 1) * 2 + 0) * 16 + 1] = '3';
        buf[((2 * 3 + 1) * 2 + 1) * 16 + 0] = '4';
        buf[((2 * 3 + 1) * 2 + 1) * 16 + 1] = '4';
        buf[((1 * 3 + 0) * 2 + 1) * 16 + 0] = '4';
        buf[((1 * 3 + 0) * 2 + 1) * 16 + 1] = '5';
        buf[((1 * 3 + 1) * 2 + 1) * 16 + 0] = '4';
        buf[((1 * 3 + 1) * 2 + 1) * 16 + 1] = '6';
        buf[((1 * 3 + 2) * 2 + 1) * 16 + 0] = '4';
        buf[((1 * 3 + 2) * 2 + 1) * 16 + 1] = '7';
        buf[((0 * 3 + 0) * 2 + 0) * 16 + 0] = '4';
        buf[((0 * 3 + 0) * 2 + 0) * 16 + 1] = '8';
        buf[((1 * 3 + 0) * 2 + 0) * 16 + 0] = '4';
        buf[((1 * 3 + 0) * 2 + 0) * 16 + 1] = '9';
        buf[((2 * 3 + 0) * 2 + 0) * 16 + 0] = '5';
        buf[((2 * 3 + 0) * 2 + 0) * 16 + 1] = '0';
        buf[((3 * 3 + 0) * 2 + 0) * 16 + 0] = '5';
        buf[((3 * 3 + 0) * 2 + 0) * 16 + 1] = '1';
        const char* string_array[4][3][2];
        for (int i = 0; i < 4; ++i)
            for (int j = 0; j < 3; ++j)
                for (int k = 0; k < 2; ++k)
                    string_array[i][j][k] = buf.data() + ((i * 3 + j) * 2 + k) * 16;
        e_string_0d(string_array[3][2][1]);
        e_string_1d(&string_array[2][1][0]);
        e_string_2d(&string_array[1][0][0]);
        e_string_3d(&string_array[0][0][0]);
    }

    {
        svBitVecVal bit7_array[4][3][2][1];
        set_values(bit7_array, 7);
        e_bit7_0d(bit7_array[3][2][1]);
        e_bit7_1d(bit7_array[2][1][0]);
        e_bit7_2d(bit7_array[1][0][0]);
        e_bit7_3d(bit7_array[0][0][0]);
    }

    {
        svBitVecVal bit121_array[4][3][2][4];
        set_values(bit121_array, 121);
        e_bit121_0d(bit121_array[3][2][1]);
        e_bit121_1d(bit121_array[2][1][0]);
        e_bit121_2d(bit121_array[1][0][0]);
        e_bit121_3d(bit121_array[0][0][0]);
    }

    {
        svLogicVecVal logic7_array[4][3][2][1];
        set_values(logic7_array, 7);
        e_logic7_0d(logic7_array[3][2][1]);
        e_logic7_1d(logic7_array[2][1][0]);
        e_logic7_2d(logic7_array[1][0][0]);
        e_logic7_3d(logic7_array[0][0][0]);
    }

    {
        svLogicVecVal logic121_array[4][3][2][4];
        set_values(logic121_array, 121);
        e_logic121_0d(logic121_array[3][2][1]);
        e_logic121_1d(logic121_array[2][1][0]);
        e_logic121_2d(logic121_array[1][0][0]);
        e_logic121_3d(logic121_array[0][0][0]);
    }

    {
        svLogicVecVal pack_struct_array[4][3][2][1];
        set_values(pack_struct_array, 7);
        e_pack_struct_0d(pack_struct_array[3][2][1]);
        e_pack_struct_1d(pack_struct_array[2][1][0]);
        e_pack_struct_2d(pack_struct_array[1][0][0]);
        e_pack_struct_3d(pack_struct_array[0][0][0]);
    }

#ifndef NO_UNPACK_STRUCT
    {
        unpack_struct_t unpack_struct_array[4][3][2];
        set_uint(unpack_struct_array[3][2][1].val, 42, 121);

        set_uint(unpack_struct_array[2][1][0].val, 43, 121);
        set_uint(unpack_struct_array[2][1][1].val, 44, 121);

        set_uint(unpack_struct_array[1][0][1].val, 45, 121);
        set_uint(unpack_struct_array[1][1][1].val, 46, 121);
        set_uint(unpack_struct_array[1][2][1].val, 47, 121);

        set_uint(unpack_struct_array[0][0][0].val, 48, 121);
        set_uint(unpack_struct_array[1][0][0].val, 49, 121);
        set_uint(unpack_struct_array[2][0][0].val, 50, 121);
        set_uint(unpack_struct_array[3][0][0].val, 51, 121);
        e_unpack_struct_0d(&unpack_struct_array[3][2][1]);
        e_unpack_struct_1d(&unpack_struct_array[2][1][0]);
        e_unpack_struct_2d(&unpack_struct_array[1][0][0]);
        e_unpack_struct_3d(&unpack_struct_array[0][0][0]);
    }
#endif
}
