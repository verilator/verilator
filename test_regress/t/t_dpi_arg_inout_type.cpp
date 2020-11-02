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
# include "Vt_dpi_arg_inout_type__Dpi.h"
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

void check_bvals(const svLogicVecVal* v, unsigned n);
void check_bvals(const svLogicVecVal* v, unsigned n) {
    for (unsigned i = 0; i < n; i++) {
        if (v[i].bval != 0) {
            printf(__FILE__ ":%d Bad svLogicVecVal bval\n", __LINE__);
            abort();
        }
    }
}

void set_bvals(svLogicVecVal* v, unsigned n);
void set_bvals(svLogicVecVal* v, unsigned n) {
    for (unsigned i = 0; i < n; i++) v[i].bval = 0;
}

// Basic types as per IEEE 1800-2017 35.5.6
void i_byte(char* x) {
    static int n = 0;
    if (*x != 10 - n++) stop();
    *x += 100;
}

void i_byte_unsigned(unsigned char* x) {
    static int n = 0;
    if (*x != 20 - n++) stop();
    *x += 200;
}

void i_shortint(short* x) {
    static int n = 0;
    if (*x != 30 - n++) stop();
    *x += 300;
}

void i_shortint_unsigned(unsigned short* x) {
    static int n = 0;
    if (*x != 40 - n++) stop();
    *x += 400;
}

void i_int(int* x) {
    static int n = 0;
    if (*x != 50 - n++) stop();
    *x += 500;
}

void i_int_unsigned(unsigned* x) {
    static int n = 0;
    if (*x != 60 - n++) stop();
    *x += 600;
}

void i_longint(sv_longint_t* x) {
    static int n = 0;
    if (*x != 70 - n++) stop();
    *x += 700;
}

void i_longint_unsigned(sv_longint_unsigned_t* x) {
    static int n = 0;
    if (*x != 80 - n++) stop();
    *x += 800;
}

#ifndef NO_TIME
void i_time(svLogicVecVal* x) {
    static int n = 0;
    if (x[0].aval != 90 - n++) stop();
    if (x[1].aval != 0) stop();
    check_bvals(x, 2);
    x[0].aval += 900;
}
#endif

#ifndef NO_INTEGER
void i_integer(svLogicVecVal* x) {
    static int n = 0;
    if (x[0].aval != 100 - n++) stop();
    check_bvals(x, 1);
    x[0].aval += 1000;
}
#endif

void i_real(double* x) {
    static int n = 0;
    if (*x != (-2.0 * n++ - 1.0) / 2.0) stop();
    *x += -100.0;
}

#ifndef NO_SHORTREAL
void i_shortreal(float* x) {
    static int n = 0;
    if (*x != (-4.0f * n++ - 1.0f) / 4.0f) stop();
    *x += -200.0f;
}
#endif

void i_chandle(void** x) {
    static int n = 0;
    printf("i_chandle %d\n", n);
    if (*x) stop();
    *x = (n % 2) ? reinterpret_cast<void*>(&i_chandle) : 0;
    n++;
}

void i_string(const char** x) {
    static int n = 0;
    printf("i_string %d\n", n);
    if (n++ % 2 == 0) {
        if (strcmp(*x, "Hello") != 0) stop();
        *x = "Good";
    } else {
        if (strcmp(*x, "World") != 0) stop();
        *x = "Bye";
    }
}

void i_bit(svBit* x) {
    static int n = 0;
    printf("i_bit %d\n", n);
    if (*x != !(n++ % 2)) stop();
    *x ^= 1;
}

void i_logic(svLogic* x) {
    static int n = 0;
    printf("i_logic %d\n", n);
    if (*x != n++ % 2) stop();
    *x ^= 1;
}

// Basic types via typedefs
void i_byte_t(char* x) {
    static int n = 0;
    if (*x != 10 - n) stop();
    *x += 101;
    n += 2;
}

void i_byte_unsigned_t(unsigned char* x) {
    static int n = 0;
    if (*x != 20 - n) stop();
    *x += 202;
    n += 2;
}

void i_shortint_t(short* x) {
    static int n = 0;
    if (*x != 30 - n) stop();
    *x += 303;
    n += 2;
}

void i_shortint_unsigned_t(unsigned short* x) {
    static int n = 0;
    if (*x != 40 - n) stop();
    *x += 404;
    n += 2;
}

void i_int_t(int* x) {
    static int n = 0;
    if (*x != 50 - n) stop();
    *x += 505;
    n += 2;
}

void i_int_unsigned_t(unsigned* x) {
    static int n = 0;
    if (*x != 60 - n) stop();
    *x += 606;
    n += 2;
}

void i_longint_t(sv_longint_t* x) {
    static int n = 0;
    if (*x != 70 - n) stop();
    *x += 707;
    n += 2;
}

void i_longint_unsigned_t(sv_longint_unsigned_t* x) {
    static int n = 0;
    if (*x != 80 - n) stop();
    *x += 808;
    n += 2;
}

#ifndef NO_TIME
void i_time_t(svLogicVecVal* x) {
    static int n = 0;
    if (x[0].aval != 90 - n) stop();
    if (x[1].aval != 0) stop();
    check_bvals(x, 2);
    x[0].aval += 909;
    n += 2;
}
#endif

#ifndef NO_INTEGER
void i_integer_t(svLogicVecVal* x) {
    static int n = 0;
    if (x[0].aval != 100 - n) stop();
    check_bvals(x, 1);
    x[0].aval += 1001;
    n += 2;
}
#endif

void i_real_t(double* x) {
    static int n = 0;
    if (*x != (-2.0 * n - 1.0) / 2.0) stop();
    *x += -111.0;
    n += 2;
}

#ifndef NO_SHORTREAL
void i_shortreal_t(float* x) {
    static int n = 0;
    if (*x != (-4.0f * n - 1.0f) / 4.0f) stop();
    *x += -222.0f;
    n += 2;
}
#endif

void i_chandle_t(void** x) {
    static int n = 0;
    printf("i_chandle_t %d\n", n);
    if (*x) stop();
    *x = (n % 2) ? 0 : reinterpret_cast<void*>(&i_chandle_t);
    n++;
}

void i_string_t(const char** x) {
    static int n = 0;
    printf("i_string_t %d\n", n);
    if (n++ % 2 == 0) {
        if (strcmp(*x, "World") != 0) stop();
        *x = "Bye";
    } else {
        if (strcmp(*x, "Hello") != 0) stop();
        *x = "Good";
    }
}

void i_bit_t(svBit* x) {
    static int n = 0;
    printf("i_bit_t %d\n", n);
    if (*x != !(n++ % 2)) stop();
    *x ^= 1;
}

void i_logic_t(svLogic* x) {
    static int n = 0;
    printf("i_logic_t %d\n", n);
    if (*x != n++ % 2) stop();
    *x ^= 1;
}

// 2-state packed arrays
void i_array_2_state_1(svBitVecVal* x) {
    static int n = 0;
    printf("i_array_2_state_1 %d\n", n);
    *x &= 1;
    if (*x != !(n++ % 2)) stop();
    *x ^= 1;
}

void i_array_2_state_32(svBitVecVal* x) {
    static int n = 0;
    printf("i_array_2_state_32 %d\n", n);
    if (*x != 0xffffffffU << n) stop();
    *x >>= n;
    n++;
}

void i_array_2_state_33(svBitVecVal* x) {
    static int n = 0;
    printf("i_array_2_state_33 %d\n", n);
    x[1] &= 1;
    if (x[0] != 0xffffffffU << n) stop();
    if (x[1] != 1) stop();
    if (n > 0) {
        x[0] = x[1] << (32 - n) | x[0] >> n;
        x[1] = x[1] >> n;
    }
    n++;
}

void i_array_2_state_64(svBitVecVal* x) {
    static int n = 0;
    printf("i_array_2_state_64 %d\n", n);
    if (x[0] != 0xffffffffU << n) stop();
    if (x[1] != -1) stop();
    if (n > 0) {
        x[0] = x[1] << (32 - n) | x[0] >> n;
        x[1] = x[1] >> n;
    }
    n++;
}

void i_array_2_state_65(svBitVecVal* x) {
    static int n = 0;
    printf("i_array_2_state_65 %d\n", n);
    x[2] &= 1;
    if (x[0] != 0xffffffffU << n) stop();
    if (x[1] != -1) stop();
    if (x[2] != 1) stop();
    if (n > 0) {
        x[0] = -1;
        x[1] = x[2] << (32 - n) | x[1] >> n;
        x[2] = x[2] >> n;
    }
    n++;
}

void i_array_2_state_128(svBitVecVal* x) {
    static int n = 0;
    printf("i_array_2_state_128 %d\n", n);
    if (x[0] != 0xffffffffU << n) stop();
    if (x[1] != -1) stop();
    if (x[2] != -1) stop();
    if (x[3] != -1) stop();
    if (n > 0) {
        x[0] = -1;
        x[2] = x[3] << (32 - n) | x[2] >> n;
        x[3] = x[3] >> n;
    }
    n++;
}

// 2-state packed structures
void i_struct_2_state_1(svBitVecVal* x) {
    static int n = 0;
    printf("i_struct_2_state_1 %d\n", n);
    *x &= 1;
    if (*x != !(n++ % 2)) stop();
    *x ^= 1;
}

void i_struct_2_state_32(svBitVecVal* x) {
    static int n = 0;
    printf("i_struct_2_state_32 %d\n", n);
    if (*x != 0xffffffffU << n) stop();
    *x >>= n;
    n++;
}

void i_struct_2_state_33(svBitVecVal* x) {
    static int n = 0;
    printf("i_struct_2_state_33 %d\n", n);
    x[1] &= 1;
    if (x[0] != 0xffffffffU << n) stop();
    if (x[1] != 1) stop();
    if (n > 0) {
        x[0] = x[1] << (32 - n) | x[0] >> n;
        x[1] = x[1] >> n;
    }
    n++;
}

void i_struct_2_state_64(svBitVecVal* x) {
    static int n = 0;
    printf("i_struct_2_state_64 %d\n", n);
    if (x[0] != 0xffffffffU << n) stop();
    if (x[1] != -1) stop();
    if (n > 0) {
        x[0] = x[1] << (32 - n) | x[0] >> n;
        x[1] = x[1] >> n;
    }
    n++;
}

void i_struct_2_state_65(svBitVecVal* x) {
    static int n = 0;
    printf("i_struct_2_state_65 %d\n", n);
    x[2] &= 1;
    if (x[0] != 0xffffffffU << n) stop();
    if (x[1] != -1) stop();
    if (x[2] != 1) stop();
    if (n > 0) {
        x[0] = -1;
        x[1] = x[2] << (32 - n) | x[1] >> n;
        x[2] = x[2] >> n;
    }
    n++;
}

void i_struct_2_state_128(svBitVecVal* x) {
    static int n = 0;
    printf("i_struct_2_state_128 %d\n", n);
    if (x[0] != 0xffffffffU << n) stop();
    if (x[1] != -1) stop();
    if (x[2] != -1) stop();
    if (x[3] != -1) stop();
    if (n > 0) {
        x[0] = -1;
        x[2] = x[3] << (32 - n) | x[2] >> n;
        x[3] = x[3] >> n;
    }
    n++;
}

// 2-state packed unions
void i_union_2_state_1(svBitVecVal* x) {
    static int n = 0;
    printf("i_union_2_state_1 %d\n", n);
    *x &= 1;
    if (*x != !(n++ % 2)) stop();
    *x ^= 1;
}

void i_union_2_state_32(svBitVecVal* x) {
    static int n = 0;
    printf("i_union_2_state_32 %d\n", n);
    if (*x != 0xffffffffU << n) stop();
    *x >>= n;
    n++;
}

void i_union_2_state_33(svBitVecVal* x) {
    static int n = 0;
    printf("i_union_2_state_33 %d\n", n);
    x[1] &= 1;
    if (x[0] != 0xffffffffU << n) stop();
    if (x[1] != 1) stop();
    if (n > 0) {
        x[0] = x[1] << (32 - n) | x[0] >> n;
        x[1] = x[1] >> n;
    }
    n++;
}

void i_union_2_state_64(svBitVecVal* x) {
    static int n = 0;
    printf("i_union_2_state_64 %d\n", n);
    if (x[0] != 0xffffffffU << n) stop();
    if (x[1] != -1) stop();
    if (n > 0) {
        x[0] = x[1] << (32 - n) | x[0] >> n;
        x[1] = x[1] >> n;
    }
    n++;
}

void i_union_2_state_65(svBitVecVal* x) {
    static int n = 0;
    printf("i_union_2_state_65 %d\n", n);
    x[2] &= 1;
    if (x[0] != 0xffffffffU << n) stop();
    if (x[1] != -1) stop();
    if (x[2] != 1) stop();
    if (n > 0) {
        x[0] = -1;
        x[1] = x[2] << (32 - n) | x[1] >> n;
        x[2] = x[2] >> n;
    }
    n++;
}

void i_union_2_state_128(svBitVecVal* x) {
    static int n = 0;
    printf("i_union_2_state_128 %d\n", n);
    if (x[0] != 0xffffffffU << n) stop();
    if (x[1] != -1) stop();
    if (x[2] != -1) stop();
    if (x[3] != -1) stop();
    if (n > 0) {
        x[0] = -1;
        x[2] = x[3] << (32 - n) | x[2] >> n;
        x[3] = x[3] >> n;
    }
    n++;
}

// 4-state packed arrays
void i_array_4_state_1(svLogicVecVal* x) {
    static int n = 0;
    printf("i_array_4_state_1 %d\n", n);
    x[0].aval &= 1;
    if (x[0].aval != !(n++ % 2)) stop();
    check_bvals(x, 1);
    x[0].aval ^= 1;
}

void i_array_4_state_32(svLogicVecVal* x) {
    static int n = 0;
    printf("i_array_4_state_32 %d\n", n);
    if (x[0].aval != 0xffffffffU << n) stop();
    check_bvals(x, 1);
    x[0].aval >>= n;
    n++;
}

void i_array_4_state_33(svLogicVecVal* x) {
    static int n = 0;
    printf("i_array_4_state_33 %d\n", n);
    x[1].aval &= 1;
    if (x[0].aval != 0xffffffffU << n) stop();
    if (x[1].aval != 1) stop();
    check_bvals(x, 2);
    if (n > 0) {
        x[0].aval = x[1].aval << (32 - n) | x[0].aval >> n;
        x[1].aval = x[1].aval >> n;
    }
    n++;
}

void i_array_4_state_64(svLogicVecVal* x) {
    static int n = 0;
    printf("i_array_4_state_64 %d\n", n);
    if (x[0].aval != 0xffffffffU << n) stop();
    if (x[1].aval != -1) stop();
    check_bvals(x, 2);
    if (n > 0) {
        x[0].aval = x[1].aval << (32 - n) | x[0].aval >> n;
        x[1].aval = x[1].aval >> n;
    }
    n++;
}

void i_array_4_state_65(svLogicVecVal* x) {
    static int n = 0;
    printf("i_array_4_state_65 %d\n", n);
    x[2].aval &= 1;
    if (x[0].aval != 0xffffffffU << n) stop();
    if (x[1].aval != -1) stop();
    if (x[2].aval != 1) stop();
    check_bvals(x, 3);
    if (n > 0) {
        x[0].aval = -1;
        x[1].aval = x[2].aval << (32 - n) | x[1].aval >> n;
        x[2].aval = x[2].aval >> n;
    }
    n++;
}

void i_array_4_state_128(svLogicVecVal* x) {
    static int n = 0;
    printf("i_array_4_state_128 %d\n", n);
    if (x[0].aval != 0xffffffffU << n) stop();
    if (x[1].aval != -1) stop();
    if (x[2].aval != -1) stop();
    if (x[3].aval != -1) stop();
    check_bvals(x, 4);
    if (n > 0) {
        x[0].aval = -1;
        x[2].aval = x[3].aval << (32 - n) | x[2].aval >> n;
        x[3].aval = x[3].aval >> n;
    }
    n++;
}

// 4-state packed structures
void i_struct_4_state_1(svLogicVecVal* x) {
    static int n = 0;
    printf("i_struct_4_state_1 %d\n", n);
    x[0].aval &= 1;
    if (x[0].aval != !(n++ % 2)) stop();
    check_bvals(x, 1);
    x[0].aval ^= 1;
}

void i_struct_4_state_32(svLogicVecVal* x) {
    static int n = 0;
    printf("i_struct_4_state_32 %d\n", n);
    if (x[0].aval != 0xffffffffU << n) stop();
    check_bvals(x, 1);
    x[0].aval >>= n;
    n++;
}

void i_struct_4_state_33(svLogicVecVal* x) {
    static int n = 0;
    printf("i_struct_4_state_33 %d\n", n);
    x[1].aval &= 1;
    if (x[0].aval != 0xffffffffU << n) stop();
    if (x[1].aval != 1) stop();
    check_bvals(x, 2);
    if (n > 0) {
        x[0].aval = x[1].aval << (32 - n) | x[0].aval >> n;
        x[1].aval = x[1].aval >> n;
    }
    n++;
}

void i_struct_4_state_64(svLogicVecVal* x) {
    static int n = 0;
    printf("i_struct_4_state_64 %d\n", n);
    if (x[0].aval != 0xffffffffU << n) stop();
    if (x[1].aval != -1) stop();
    check_bvals(x, 2);
    if (n > 0) {
        x[0].aval = x[1].aval << (32 - n) | x[0].aval >> n;
        x[1].aval = x[1].aval >> n;
    }
    n++;
}

void i_struct_4_state_65(svLogicVecVal* x) {
    static int n = 0;
    printf("i_struct_4_state_65 %d\n", n);
    x[2].aval &= 1;
    if (x[0].aval != 0xffffffffU << n) stop();
    if (x[1].aval != -1) stop();
    if (x[2].aval != 1) stop();
    check_bvals(x, 3);
    if (n > 0) {
        x[0].aval = -1;
        x[1].aval = x[2].aval << (32 - n) | x[1].aval >> n;
        x[2].aval = x[2].aval >> n;
    }
    n++;
}

void i_struct_4_state_128(svLogicVecVal* x) {
    static int n = 0;
    printf("i_struct_4_state_128 %d\n", n);
    if (x[0].aval != 0xffffffffU << n) stop();
    if (x[1].aval != -1) stop();
    if (x[2].aval != -1) stop();
    if (x[3].aval != -1) stop();
    check_bvals(x, 4);
    if (n > 0) {
        x[0].aval = -1;
        x[2].aval = x[3].aval << (32 - n) | x[2].aval >> n;
        x[3].aval = x[3].aval >> n;
    }
    n++;
}

// 4-state packed unions
void i_union_4_state_1(svLogicVecVal* x) {
    static int n = 0;
    printf("i_union_4_state_1 %d\n", n);
    x[0].aval &= 1;
    if (x[0].aval != !(n++ % 2)) stop();
    check_bvals(x, 1);
    x[0].aval ^= 1;
}

void i_union_4_state_32(svLogicVecVal* x) {
    static int n = 0;
    printf("i_union_4_state_32 %d\n", n);
    if (x[0].aval != 0xffffffffU << n) stop();
    check_bvals(x, 1);
    x[0].aval >>= n;
    n++;
}

void i_union_4_state_33(svLogicVecVal* x) {
    static int n = 0;
    printf("i_union_4_state_33 %d\n", n);
    x[1].aval &= 1;
    if (x[0].aval != 0xffffffffU << n) stop();
    if (x[1].aval != 1) stop();
    check_bvals(x, 2);
    if (n > 0) {
        x[0].aval = x[1].aval << (32 - n) | x[0].aval >> n;
        x[1].aval = x[1].aval >> n;
    }
    n++;
}

void i_union_4_state_64(svLogicVecVal* x) {
    static int n = 0;
    printf("i_union_4_state_64 %d\n", n);
    if (x[0].aval != 0xffffffffU << n) stop();
    if (x[1].aval != -1) stop();
    check_bvals(x, 2);
    if (n > 0) {
        x[0].aval = x[1].aval << (32 - n) | x[0].aval >> n;
        x[1].aval = x[1].aval >> n;
    }
    n++;
}

void i_union_4_state_65(svLogicVecVal* x) {
    static int n = 0;
    printf("i_union_4_state_65 %d\n", n);
    x[2].aval &= 1;
    if (x[0].aval != 0xffffffffU << n) stop();
    if (x[1].aval != -1) stop();
    if (x[2].aval != 1) stop();
    check_bvals(x, 3);
    if (n > 0) {
        x[0].aval = -1;
        x[1].aval = x[2].aval << (32 - n) | x[1].aval >> n;
        x[2].aval = x[2].aval >> n;
    }
    n++;
}

void i_union_4_state_128(svLogicVecVal* x) {
    static int n = 0;
    printf("i_union_4_state_128 %d\n", n);
    if (x[0].aval != 0xffffffffU << n) stop();
    if (x[1].aval != -1) stop();
    if (x[2].aval != -1) stop();
    if (x[3].aval != -1) stop();
    check_bvals(x, 4);
    if (n > 0) {
        x[0].aval = -1;
        x[2].aval = x[3].aval << (32 - n) | x[2].aval >> n;
        x[3].aval = x[3].aval >> n;
    }
    n++;
}

//======================================================================
// Check exported functions
//======================================================================

void check_exports() {
    static int n = 0;

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

#ifndef NO_TIME
    set_bvals(x_time, 2);
    set_bvals(x_time_t, 2);
#endif
#ifndef NO_INTEGER
    set_bvals(x_integer, 1);
    set_bvals(x_integer_t, 1);
#endif

    set_bvals(x_array_4_state_1, 1);
    set_bvals(x_array_4_state_32, 1);
    set_bvals(x_array_4_state_33, 2);
    set_bvals(x_array_4_state_64, 2);
    set_bvals(x_array_4_state_65, 3);
    set_bvals(x_array_4_state_128, 4);

    set_bvals(x_struct_4_state_1, 1);
    set_bvals(x_struct_4_state_32, 1);
    set_bvals(x_struct_4_state_33, 2);
    set_bvals(x_struct_4_state_64, 2);
    set_bvals(x_struct_4_state_65, 3);
    set_bvals(x_struct_4_state_128, 4);

    set_bvals(x_union_4_state_1, 1);
    set_bvals(x_union_4_state_32, 1);
    set_bvals(x_union_4_state_33, 2);
    set_bvals(x_union_4_state_64, 2);
    set_bvals(x_union_4_state_65, 3);
    set_bvals(x_union_4_state_128, 4);

    // Basic types as per IEEE 1800-2017 35.5.6
    x_byte = 10 + n;
    e_byte(&x_byte);
    if (x_byte != 110 + n) stop();

    x_byte_unsigned = 20 + n;
    e_byte_unsigned(&x_byte_unsigned);
    if (x_byte_unsigned != 220 + n) stop();

    x_shortint = 30 + n;
    e_shortint(&x_shortint);
    if (x_shortint != 330 + n) stop();

    x_shortint_unsigned = 40 + n;
    e_shortint_unsigned(&x_shortint_unsigned);
    if (x_shortint_unsigned != 440 + n) stop();

    x_int = 50 + n;
    e_int(&x_int);
    if (x_int != 550 + n) stop();

    x_int_unsigned = 60 + n;
    e_int_unsigned(&x_int_unsigned);
    if (x_int_unsigned != 660 + n) stop();

    x_longint = 70 + n;
    e_longint(&x_longint);
    if (x_longint != 770 + n) stop();

    x_longint_unsigned = 80 + n;
    e_longint_unsigned(&x_longint_unsigned);
    if (x_longint_unsigned != 880 + n) stop();

#ifndef NO_TIME
    x_time[0].aval = 90 + n;
    x_time[1].aval = 0;
    e_time(x_time);
    if (x_time[0].aval != 990 + n || x_time[1].aval != 0) stop();
    check_bvals(x_time, 2);
#endif

#ifndef NO_INTEGER
    x_integer[0].aval = 100 + n;
    e_integer(x_integer);
    if (x_integer[0].aval != 1100 + n) stop();
    check_bvals(x_integer, 1);
#endif

    x_real = 1.0 * n + 0.50;
    e_real(&x_real);
    if (x_real != 100.0 + 1.0 * n + 0.5) stop();

#ifndef NO_SHORTREAL
    x_shortreal = 1.0f * n + 0.25f;
    e_shortreal(&x_shortreal);
    if (x_shortreal != 200.0f + 1.0f * n + 0.25f) stop();
#endif

    if ((n % 2) == 0) {
        x_chandle = reinterpret_cast<void*>(&e_chandle);
        x_string = "Good";
    } else {
        x_chandle = NULL;
        x_string = "Bye";
    }
    e_chandle(&x_chandle);
    e_string(&x_string);
    if ((n % 2) == 0) {
        if (x_chandle) stop();
        if (strcmp(x_string, "Hello") != 0) stop();
    } else {
        if (x_chandle) stop();
        if (strcmp(x_string, "World") != 0) stop();
    }

    x_bit = n % 2;
    e_bit(&x_bit);
    if (x_bit != !(n % 2)) stop();

    x_logic = !(n % 2);
    e_logic(&x_logic);
    if (x_logic != n % 2) stop();

    // Basic types via tyepdef
    x_byte_t = 10 + 2 * n;
    e_byte_t(&x_byte_t);
    if (x_byte_t != 111 + 2 * n) stop();

    x_byte_unsigned_t = 20 + 2 * n;
    e_byte_unsigned_t(&x_byte_unsigned_t);
    if (x_byte_unsigned_t != 222 + 2 * n) stop();

    x_shortint_t = 30 + 2 * n;
    e_shortint_t(&x_shortint_t);
    if (x_shortint_t != 333 + 2 * n) stop();

    x_shortint_unsigned_t = 40 + 2 * n;
    e_shortint_unsigned_t(&x_shortint_unsigned_t);
    if (x_shortint_unsigned_t != 444 + 2 * n) stop();

    x_int_t = 50 + 2 * n;
    e_int_t(&x_int_t);
    if (x_int_t != 555 + 2 * n) stop();

    x_int_unsigned_t = 60 + 2 * n;
    e_int_unsigned_t(&x_int_unsigned_t);
    if (x_int_unsigned_t != 666 + 2 * n) stop();

    x_longint_t = 70 + 2 * n;
    e_longint_t(&x_longint_t);
    if (x_longint_t != 777 + 2 * n) stop();

    x_longint_unsigned_t = 80 + 2 * n;
    e_longint_unsigned_t(&x_longint_unsigned_t);
    if (x_longint_unsigned_t != 888 + 2 * n) stop();

#ifndef NO_TIME
    x_time_t[0].aval = 90 + 2 * n;
    x_time_t[1].aval = 0;
    e_time_t(x_time_t);
    if (x_time_t[0].aval != 999 + 2 * n || x_time_t[1].aval != 0) stop();
    check_bvals(x_time_t, 2);
#endif

#ifndef NO_INTEGER
    x_integer_t[0].aval = 100 + 2 * n;
    e_integer_t(x_integer_t);
    if (x_integer_t[0].aval != 1101 + 2 * n) stop();
    check_bvals(x_integer_t, 1);
#endif

    x_real_t = 1.0 * (2 * n) + 0.50;
    e_real_t(&x_real_t);
    if (x_real_t != 111.0 + 1.0 * (2 * n) + 0.5) stop();

#ifndef NO_SHORTREAL
    x_shortreal_t = 1.0f * (2 * n) + 0.25f;
    e_shortreal_t(&x_shortreal_t);
    if (x_shortreal_t != 222.0f + 1.0f * (2 * n) + 0.25f) stop();
#endif

    if ((n % 2) == 0) {
        x_chandle_t = NULL;
        x_string_t = "Bye";
    } else {
        x_chandle_t = reinterpret_cast<void*>(&e_chandle_t);
        x_string_t = "Good";
    }
    e_chandle_t(&x_chandle_t);
    e_string_t(&x_string_t);
    if ((n % 2) == 0) {
        if (x_chandle_t != NULL) stop();
        if (strcmp(x_string_t, "World") != 0) stop();
    } else {
        if (x_chandle_t != NULL) stop();
        if (strcmp(x_string_t, "Hello") != 0) stop();
    }

    x_bit_t = n % 2;
    e_bit_t(&x_bit_t);
    if (x_bit_t != !(n % 2)) stop();

    x_logic_t = !(n % 2);
    e_logic_t(&x_logic_t);
    if (x_logic_t != n % 2) stop();

    const int m = n == 0 ? 0 : n - 1;

    // 2-state packed arrays
    x_array_2_state_1[0] = n % 2;
    x_array_2_state_32[0] = 0xffffffff >> n;
    x_array_2_state_33[1] = 1 >> n;
    x_array_2_state_33[0] = 0xffffffff >> m;
    x_array_2_state_64[1] = 0xffffffff >> n;
    x_array_2_state_64[0] = 0xffffffff;
    x_array_2_state_65[2] = 1 >> n;
    x_array_2_state_65[1] = 0xffffffff >> m;
    x_array_2_state_65[0] = 0xffffffff;
    x_array_2_state_128[3] = 0xffffffff >> n;
    x_array_2_state_128[2] = x_array_2_state_128[1] = x_array_2_state_128[0] = 0xffffffff;

    e_array_2_state_1(x_array_2_state_1);
    if ((x_array_2_state_1[0] & 1) != !(n % 2)) stop();

    e_array_2_state_32(x_array_2_state_32);
    if (x_array_2_state_32[0] != 0xffffffff << n) stop();

    e_array_2_state_33(x_array_2_state_33);
    if ((x_array_2_state_33[1] & 1) != 1) stop();
    if (x_array_2_state_33[0] != 0xffffffff << n) stop();

    e_array_2_state_64(x_array_2_state_64);
    if (x_array_2_state_64[1] != 0xffffffff) stop();
    if (x_array_2_state_64[0] != 0xffffffff << n) stop();

    e_array_2_state_65(x_array_2_state_65);
    if ((x_array_2_state_65[2] & 1) != 1) stop();
    if (x_array_2_state_65[1] != 0xffffffff) stop();
    if (x_array_2_state_65[0] != 0xffffffff << n) stop();

    e_array_2_state_128(x_array_2_state_128);
    if (x_array_2_state_128[3] != 0xffffffff) stop();
    if (x_array_2_state_128[2] != 0xffffffff) stop();
    if (x_array_2_state_128[1] != 0xffffffff) stop();
    if (x_array_2_state_128[0] != 0xffffffff << n) stop();

    // 2-state packed structures
    x_struct_2_state_1[0] = n % 2;
    x_struct_2_state_32[0] = 0xffffffff >> n;
    x_struct_2_state_33[1] = 1 >> n;
    x_struct_2_state_33[0] = 0xffffffff >> m;
    x_struct_2_state_64[1] = 0xffffffff >> n;
    x_struct_2_state_64[0] = 0xffffffff;
    x_struct_2_state_65[2] = 1 >> n;
    x_struct_2_state_65[1] = 0xffffffff >> m;
    x_struct_2_state_65[0] = 0xffffffff;
    x_struct_2_state_128[3] = 0xffffffff >> n;
    x_struct_2_state_128[2] = x_struct_2_state_128[1] = x_struct_2_state_128[0] = 0xffffffff;

    e_struct_2_state_1(x_struct_2_state_1);
    if ((x_struct_2_state_1[0] & 1) != !(n % 2)) stop();

    e_struct_2_state_32(x_struct_2_state_32);
    if (x_struct_2_state_32[0] != 0xffffffff << n) stop();

    e_struct_2_state_33(x_struct_2_state_33);
    if ((x_struct_2_state_33[1] & 1) != 1) stop();
    if (x_struct_2_state_33[0] != 0xffffffff << n) stop();

    e_struct_2_state_64(x_struct_2_state_64);
    if (x_struct_2_state_64[1] != 0xffffffff) stop();
    if (x_struct_2_state_64[0] != 0xffffffff << n) stop();

    e_struct_2_state_65(x_struct_2_state_65);
    if ((x_struct_2_state_65[2] & 1) != 1) stop();
    if (x_struct_2_state_65[1] != 0xffffffff) stop();
    if (x_struct_2_state_65[0] != 0xffffffff << n) stop();

    e_struct_2_state_128(x_struct_2_state_128);
    if (x_struct_2_state_128[3] != 0xffffffff) stop();
    if (x_struct_2_state_128[2] != 0xffffffff) stop();
    if (x_struct_2_state_128[1] != 0xffffffff) stop();
    if (x_struct_2_state_128[0] != 0xffffffff << n) stop();

    // 2-state packed unions
    x_union_2_state_1[0] = n % 2;
    x_union_2_state_32[0] = 0xffffffff >> n;
    x_union_2_state_33[1] = 1 >> n;
    x_union_2_state_33[0] = 0xffffffff >> m;
    x_union_2_state_64[1] = 0xffffffff >> n;
    x_union_2_state_64[0] = 0xffffffff;
    x_union_2_state_65[2] = 1 >> n;
    x_union_2_state_65[1] = 0xffffffff >> m;
    x_union_2_state_65[0] = 0xffffffff;
    x_union_2_state_128[3] = 0xffffffff >> n;
    x_union_2_state_128[2] = x_union_2_state_128[1] = x_union_2_state_128[0] = 0xffffffff;

    e_union_2_state_1(x_union_2_state_1);
    if ((x_union_2_state_1[0] & 1) != !(n % 2)) stop();

    e_union_2_state_32(x_union_2_state_32);
    if (x_union_2_state_32[0] != 0xffffffff << n) stop();

    e_union_2_state_33(x_union_2_state_33);
    if ((x_union_2_state_33[1] & 1) != 1) stop();
    if (x_union_2_state_33[0] != 0xffffffff << n) stop();

    e_union_2_state_64(x_union_2_state_64);
    if (x_union_2_state_64[1] != 0xffffffff) stop();
    if (x_union_2_state_64[0] != 0xffffffff << n) stop();

    e_union_2_state_65(x_union_2_state_65);
    if ((x_union_2_state_65[2] & 1) != 1) stop();
    if (x_union_2_state_65[1] != 0xffffffff) stop();
    if (x_union_2_state_65[0] != 0xffffffff << n) stop();

    e_union_2_state_128(x_union_2_state_128);
    if (x_union_2_state_128[3] != 0xffffffff) stop();
    if (x_union_2_state_128[2] != 0xffffffff) stop();
    if (x_union_2_state_128[1] != 0xffffffff) stop();
    if (x_union_2_state_128[0] != 0xffffffff << n) stop();

    // 4-state packed arrays
    x_array_4_state_1[0].aval = n % 2;
    x_array_4_state_32[0].aval = 0xffffffff >> n;
    x_array_4_state_33[1].aval = 1 >> n;
    x_array_4_state_33[0].aval = 0xffffffff >> m;
    x_array_4_state_64[1].aval = 0xffffffff >> n;
    x_array_4_state_64[0].aval = 0xffffffff;
    x_array_4_state_65[2].aval = 1 >> n;
    x_array_4_state_65[1].aval = 0xffffffff >> m;
    x_array_4_state_65[0].aval = 0xffffffff;
    x_array_4_state_128[3].aval = 0xffffffff >> n;
    x_array_4_state_128[2].aval = 0xffffffff;
    x_array_4_state_128[1].aval = 0xffffffff;
    x_array_4_state_128[0].aval = 0xffffffff;

    e_array_4_state_1(x_array_4_state_1);
    if ((x_array_4_state_1[0].aval & 1) != !(n % 2)) stop();

    e_array_4_state_32(x_array_4_state_32);
    if (x_array_4_state_32[0].aval != 0xffffffff << n) stop();

    e_array_4_state_33(x_array_4_state_33);
    if ((x_array_4_state_33[1].aval & 1) != 1) stop();
    if (x_array_4_state_33[0].aval != 0xffffffff << n) stop();

    e_array_4_state_64(x_array_4_state_64);
    if (x_array_4_state_64[1].aval != 0xffffffff) stop();
    if (x_array_4_state_64[0].aval != 0xffffffff << n) stop();

    e_array_4_state_65(x_array_4_state_65);
    if ((x_array_4_state_65[2].aval & 1) != 1) stop();
    if (x_array_4_state_65[1].aval != 0xffffffff) stop();
    if (x_array_4_state_65[0].aval != 0xffffffff << n) stop();

    e_array_4_state_128(x_array_4_state_128);
    if (x_array_4_state_128[3].aval != 0xffffffff) stop();
    if (x_array_4_state_128[2].aval != 0xffffffff) stop();
    if (x_array_4_state_128[1].aval != 0xffffffff) stop();
    if (x_array_4_state_128[0].aval != 0xffffffff << n) stop();

    check_bvals(x_array_4_state_1, 1);
    check_bvals(x_array_4_state_32, 1);
    check_bvals(x_array_4_state_33, 2);
    check_bvals(x_array_4_state_64, 2);
    check_bvals(x_array_4_state_65, 3);
    check_bvals(x_array_4_state_128, 4);

    // 4-state packed structures
    x_struct_4_state_1[0].aval = n % 2;
    x_struct_4_state_32[0].aval = 0xffffffff >> n;
    x_struct_4_state_33[1].aval = 1 >> n;
    x_struct_4_state_33[0].aval = 0xffffffff >> m;
    x_struct_4_state_64[1].aval = 0xffffffff >> n;
    x_struct_4_state_64[0].aval = 0xffffffff;
    x_struct_4_state_65[2].aval = 1 >> n;
    x_struct_4_state_65[1].aval = 0xffffffff >> m;
    x_struct_4_state_65[0].aval = 0xffffffff;
    x_struct_4_state_128[3].aval = 0xffffffff >> n;
    x_struct_4_state_128[2].aval = 0xffffffff;
    x_struct_4_state_128[1].aval = 0xffffffff;
    x_struct_4_state_128[0].aval = 0xffffffff;

    e_struct_4_state_1(x_struct_4_state_1);
    if ((x_struct_4_state_1[0].aval & 1) != !(n % 2)) stop();

    e_struct_4_state_32(x_struct_4_state_32);
    if (x_struct_4_state_32[0].aval != 0xffffffff << n) stop();

    e_struct_4_state_33(x_struct_4_state_33);
    if ((x_struct_4_state_33[1].aval & 1) != 1) stop();
    if (x_struct_4_state_33[0].aval != 0xffffffff << n) stop();

    e_struct_4_state_64(x_struct_4_state_64);
    if (x_struct_4_state_64[1].aval != 0xffffffff) stop();
    if (x_struct_4_state_64[0].aval != 0xffffffff << n) stop();

    e_struct_4_state_65(x_struct_4_state_65);
    if ((x_struct_4_state_65[2].aval & 1) != 1) stop();
    if (x_struct_4_state_65[1].aval != 0xffffffff) stop();
    if (x_struct_4_state_65[0].aval != 0xffffffff << n) stop();

    e_struct_4_state_128(x_struct_4_state_128);
    if (x_struct_4_state_128[3].aval != 0xffffffff) stop();
    if (x_struct_4_state_128[2].aval != 0xffffffff) stop();
    if (x_struct_4_state_128[1].aval != 0xffffffff) stop();
    if (x_struct_4_state_128[0].aval != 0xffffffff << n) stop();

    check_bvals(x_struct_4_state_1, 1);
    check_bvals(x_struct_4_state_32, 1);
    check_bvals(x_struct_4_state_33, 2);
    check_bvals(x_struct_4_state_64, 2);
    check_bvals(x_struct_4_state_65, 3);
    check_bvals(x_struct_4_state_128, 4);

    // 4-state packed unions
    x_union_4_state_1[0].aval = n % 2;
    x_union_4_state_32[0].aval = 0xffffffff >> n;
    x_union_4_state_33[1].aval = 1 >> n;
    x_union_4_state_33[0].aval = 0xffffffff >> m;
    x_union_4_state_64[1].aval = 0xffffffff >> n;
    x_union_4_state_64[0].aval = 0xffffffff;
    x_union_4_state_65[2].aval = 1 >> n;
    x_union_4_state_65[1].aval = 0xffffffff >> m;
    x_union_4_state_65[0].aval = 0xffffffff;
    x_union_4_state_128[3].aval = 0xffffffff >> n;
    x_union_4_state_128[2].aval = 0xffffffff;
    x_union_4_state_128[1].aval = 0xffffffff;
    x_union_4_state_128[0].aval = 0xffffffff;

    e_union_4_state_1(x_union_4_state_1);
    if ((x_union_4_state_1[0].aval & 1) != !(n % 2)) stop();

    e_union_4_state_32(x_union_4_state_32);
    if (x_union_4_state_32[0].aval != 0xffffffff << n) stop();

    e_union_4_state_33(x_union_4_state_33);
    if ((x_union_4_state_33[1].aval & 1) != 1) stop();
    if (x_union_4_state_33[0].aval != 0xffffffff << n) stop();

    e_union_4_state_64(x_union_4_state_64);
    if (x_union_4_state_64[1].aval != 0xffffffff) stop();
    if (x_union_4_state_64[0].aval != 0xffffffff << n) stop();

    e_union_4_state_65(x_union_4_state_65);
    if ((x_union_4_state_65[2].aval & 1) != 1) stop();
    if (x_union_4_state_65[1].aval != 0xffffffff) stop();
    if (x_union_4_state_65[0].aval != 0xffffffff << n) stop();

    e_union_4_state_128(x_union_4_state_128);
    if (x_union_4_state_128[3].aval != 0xffffffff) stop();
    if (x_union_4_state_128[2].aval != 0xffffffff) stop();
    if (x_union_4_state_128[1].aval != 0xffffffff) stop();
    if (x_union_4_state_128[0].aval != 0xffffffff << n) stop();

    check_bvals(x_union_4_state_1, 1);
    check_bvals(x_union_4_state_32, 1);
    check_bvals(x_union_4_state_33, 2);
    check_bvals(x_union_4_state_64, 2);
    check_bvals(x_union_4_state_65, 3);
    check_bvals(x_union_4_state_128, 4);

    n++;
}
