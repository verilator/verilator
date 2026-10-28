// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "svdpi.h"

#include <cstdint>
#include <utility>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

#include VM_PREFIX_INCLUDE_DPI

int errors = 0;
int dpii_failure() { return errors; }

char dpii_fill(long long base, const svOpenArrayHandle buffer) {
    for (int i = svLow(buffer, 1); i <= svHigh(buffer, 1); ++i) {
        char* const p = static_cast<char*>(svGetArrElemPtr1(buffer, i));
        if (!p) return -1;
        *p = static_cast<char>((base + i) & 0xff);
    }
    return static_cast<char>(svSize(buffer, 1));
}

// A dynamic array or queue dimension is [0:size-1] with increment -1, even if of size 0 or 1
// (IEEE 1800-2023 20.7)
int dpii_invert(const svOpenArrayHandle io) {
    const int size = svSize(io, 1);
    TEST_CHECK_EQ(svDimensions(io), 1);
    TEST_CHECK_EQ(svLeft(io, 1), 0);
    TEST_CHECK_EQ(svRight(io, 1), size - 1);
    TEST_CHECK_EQ(svLow(io, 1), 0);
    TEST_CHECK_EQ(svHigh(io, 1), size - 1);
    TEST_CHECK_EQ(svIncrement(io, 1), -1);
    TEST_CHECK_EQ(svSizeOfArray(io), size);
    for (int i = svLow(io, 1); i <= svHigh(io, 1); ++i) {
        char* const p = static_cast<char*>(svGetArrElemPtr1(io, i));
        *p = static_cast<char>(~*p ^ i);
    }
    return size;
}

int dpii_invert_kw(const svOpenArrayHandle io) { return dpii_invert(io); }

void dpii_swap(const svOpenArrayHandle a, const svOpenArrayHandle b) {
    TEST_CHECK_EQ(svSize(a, 1), svSize(b, 1));
    for (int i = 0; i < svSize(a, 1); ++i) {
        std::swap(*static_cast<int*>(svGetArrElemPtr1(a, svLow(a, 1) + i)),
                  *static_cast<int*>(svGetArrElemPtr1(b, svLow(b, 1) + i)));
    }
}

void* dpii_handle(int v) { return reinterpret_cast<void*>(static_cast<intptr_t>(v)); }

long long dpii_sum_handles(const svOpenArrayHandle h) {
    long long sum = 0;
    for (int i = svLow(h, 1); i <= svHigh(h, 1); ++i) {
        sum += reinterpret_cast<intptr_t>(*static_cast<void* const*>(svGetArrElemPtr1(h, i)));
    }
    return sum;
}

int dpii_sum(const svOpenArrayHandle i) {
    const int* const datap = static_cast<const int*>(svGetArrayPtr(i));
    const int size = svSizeOfArray(i) / sizeof(int);
    TEST_CHECK_EQ(size, svSize(i, 1));
    unsigned sum = 0;
    for (int k = 0; k < size; ++k) sum += datap[k];
    return static_cast<int>(sum);
}

void dpii_invert2(const svOpenArrayHandle io) {
    TEST_CHECK_EQ(svDimensions(io), 2);
    for (int a = svLow(io, 1); a <= svHigh(io, 1); ++a) {
        for (int b = svLow(io, 2); b <= svHigh(io, 2); ++b) {
            int* const p = static_cast<int*>(svGetArrElemPtr2(io, a, b));
            *p = ~*p ^ (a << 8) ^ b;
        }
    }
}

void dpii_invert_wide(const svOpenArrayHandle io) {
    static constexpr int WORDS = SV_PACKED_DATA_NELEMS(95);
    for (int i = svLow(io, 1); i <= svHigh(io, 1); ++i) {
        svBitVecVal vec[WORDS];
        svGetBitArrElem1VecVal(vec, io, i);
        for (int w = 0; w < WORDS; ++w) vec[w] = ~vec[w];
        vec[0] ^= i;
        vec[WORDS - 1] &= 0x7fffffff;
        svPutBitArrElem1VecVal(io, vec, i);
    }
}

// Returns the low 'width' bits of 'value', sign extended
static int signExtend(uint32_t value, int width) {
    const uint32_t sign = 1U << (width - 1);
    return static_cast<int>((value & ((sign << 1) - 1)) ^ sign) - static_cast<int>(sign);
}

void dpii_negate_logic(const svOpenArrayHandle io) {
    for (int i = svLow(io, 1); i <= svHigh(io, 1); ++i) {
        svLogicVecVal vec;
        svGetLogicArrElem1VecVal(&vec, io, i);
        TEST_CHECK_EQ(vec.bval, 0U);
        vec.aval = static_cast<uint32_t>(-signExtend(vec.aval, 15)) & 0x7fff;
        svPutLogicArrElem1VecVal(io, &vec, i);
    }
}

void dpii_invert_logic(const svOpenArrayHandle io) {
    for (int i = svLow(io, 1); i <= svHigh(io, 1); ++i) {
        svPutLogicArrElem1(io, svGetLogicArrElem1(io, i) == sv_0 ? sv_1 : sv_0, i);
    }
}

void dpii_reverse_enum(const svOpenArrayHandle io) {
    for (int i = svLow(io, 1), j = svHigh(io, 1); i < j; ++i, --j) {
        svBitVecVal a;
        svBitVecVal b;
        svGetBitArrElem1VecVal(&a, io, i);
        svGetBitArrElem1VecVal(&b, io, j);
        svPutBitArrElem1VecVal(io, &b, i);
        svPutBitArrElem1VecVal(io, &a, j);
    }
}

// Of elements of 'struct packed {bit [3:0] tag; bit signed [10:0] value;}'
void dpii_update_pair(const svOpenArrayHandle io) {
    for (int i = svLow(io, 1); i <= svHigh(io, 1); ++i) {
        svBitVecVal vec;
        svGetBitArrElem1VecVal(&vec, io, i);
        const uint32_t tag = (vec >> 11) + 1;
        const int value = -signExtend(vec, 11);
        vec = ((tag & 0xf) << 11) | (static_cast<uint32_t>(value) & 0x7ff);
        svPutBitArrElem1VecVal(io, &vec, i);
    }
}

int dpii_size(const svOpenArrayHandle i) { return svSize(i, 1); }

double dpii_sum_real(const svOpenArrayHandle i) {
    const double* const datap = static_cast<const double*>(svGetArrayPtr(i));
    double sum = 0;
    for (int k = 0; k < svSize(i, 1); ++k) sum += datap[k];
    return sum;
}

void dpii_double(const svOpenArrayHandle io) {
    double* const datap = static_cast<double*>(svGetArrayPtr(io));
    for (int k = 0; k < svSize(io, 1); ++k) datap[k] *= 2;
}
