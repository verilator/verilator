// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2024 by Kefa Chen. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************

#include <verilated.h>

#include VM_PREFIX_INCLUDE

#include "TestCheck.h"

/*
typedef logic [5:0] udata6_t;

typedef union packed {
  udata6_t    a;
  logic [2:0] b;
} sub_t;

typedef struct packed {
  logic [40:0]   a;
  udata6_t [3:0] b;
  sub_t          c;
} in_t  ;

typedef struct packed {
  udata6_t [3:0] b;
  sub_t          c;
  logic [40:0]   a;
} out_t ;
*/

#define EXPORTED_STRUCT_NAME(STRUCT_NAME, NUMBER) VM_PREFIX##_##STRUCT_NAME##__struct__##NUMBER
#define EXPORTED_UNION_NAME(UNION_NAME, NUMBER) VM_PREFIX##_##UNION_NMAE##__union__##NUMBER
#define SUB_T EXPORTED_UNION_NAME(sub_t, 0)
#define IN_T EXPORTED_STRUCT_NAME(in_t, 0)
#define OUT_T EXPORTED_STRUCT_NAME(out_t, 0)

/*
01110001
*/

template <typename OutWordT, typename InWordT>
void alignedBitHelper2(OutWordT* outWords, uint32_t outLsB, const InWordT* inWords, uint32_t inLsB,
                       uint32_t width) {
    if (width == 0) return;
    uint32_t outSize = sizeof(OutWordT);
    uint32_t outIndexOff = outLsB / outSize;
    uint32_t outByteOff = outLsB % outSize;

    uint32_t inSize = sizeof(InWordT);
    uint32_t inIndexOff = inLsB / inSize;
    uint32_t inByteOff = inLsB % inSize;

    OutWordT widthMask
        = width >= outSize * 8 ? ~(OutWordT)0 : (((OutWordT)1 << width) - 1) << (8 * outByteOff);
    OutWordT outMask = 0;
    OutWordT outWord = 0;

    uint32_t cnt = 0;
    while (width) {
        uint8_t byte = uint8_t(inWords[inIndexOff] >> (8 * inByteOff));
        outWord |= (OutWordT)byte << (8 * outByteOff);
        outMask |= (OutWordT)0xffU << (8 * outByteOff);
        ++inByteOff;
        if (inByteOff == inSize) {
            inByteOff = 0;
            ++inIndexOff;
        }
        ++outByteOff;
        ++cnt;
        if (outByteOff == outSize || cnt * 8 >= width) {
            outMask &= widthMask;
            outWords[outIndexOff] = (outWord & outMask) | (outWords[outIndexOff] & ~outMask);
            outWord = 0;
            outByteOff = 0;
            ++outIndexOff;
            width -= std::min(cnt * 8, width);
            cnt = 0;
            widthMask = width >= outSize * 8 ? ~(OutWordT)0 : ((OutWordT)1 << width) - 1;
        }
    }
}

template <typename OutWordT, typename InWordT>
void alignedBitHelper(OutWordT* outWords, uint32_t outLsB, const InWordT* inWords, uint32_t inLsb,
                      uint32_t width) {
    if (width == 0) return;
    if (inLsb % 8 == 0) {
        alignedBitHelper2(outWords, outLsB, inWords, inLsb / 8, width);
        return;
    }
    // inLsb % 8 != 0
    uint32_t outSize = sizeof(OutWordT);
    uint32_t outIndexOff = outLsB / outSize;
    uint32_t outByteOff = outLsB % outSize;

    uint32_t inSize = sizeof(InWordT);
    uint32_t inIndexOff = inLsb / 8 / inSize;
    uint32_t inByteOff = (inLsb / 8) % inSize;
    uint32_t inBitOff = inLsb % 8;

    OutWordT outWord = 0;
    OutWordT outMask = 0;
    OutWordT widthMask;
    if (width + outByteOff * 8 >= outSize * 8)
        widthMask = ~(OutWordT)0;
    else
        widthMask = ((OutWordT)1 << (width + outByteOff * 8)) - 1;

    uint8_t byte = uint8_t(inWords[inIndexOff] >> (8 * inByteOff)) >> inBitOff;
    uint32_t validBits = 8 - inBitOff;

    ++inByteOff;
    if (inByteOff == inSize) {
        inByteOff = 0;
        ++inIndexOff;
    }
    uint32_t cnt = 0;
    while (width) {
        if (validBits >= width) {
            outWord = (OutWordT)byte << (8 * outByteOff);
            outMask = (((OutWordT)1 << width) - 1) << (8 * outByteOff);
            outWords[outIndexOff] = (outWords[outIndexOff] & ~outMask) | (outWord & outMask);
            return;
        }
        uint8_t newByte = uint8_t(inWords[inIndexOff] >> (8 * inByteOff));
        byte |= newByte << validBits;
        outWord |= (OutWordT)byte << (8 * outByteOff);
        outMask |= (OutWordT)0xffU << (8 * outByteOff);
        byte = newByte >> (8 - validBits);

        ++outByteOff;
        ++cnt;
        if (outByteOff == outSize || cnt * 8 + validBits >= width) {
            outMask &= widthMask;
            outWords[outIndexOff] = (outWord & outMask) | (outWords[outIndexOff] & ~outMask);
            outWord = 0;
            width -= std::min(cnt * 8, width);
            cnt = 0;

            if (outByteOff == outSize) {
                outByteOff = 0;
                ++outIndexOff;
            }
            if (width >= outSize * 8)
                widthMask = ~(OutWordT)0;
            else
                widthMask = ((OutWordT)1 << width) - 1;
        }
        ++inByteOff;
        if (inByteOff == inSize) {
            inByteOff = 0;
            ++inIndexOff;
        }
    }
}

template <typename OutWordT, typename InWordT>
void bitHelper(OutWordT* outWords, uint32_t outLsb, const InWordT* inWords, uint32_t inLsb,
               uint32_t width) {
    uint32_t outBitOff = outLsb % 8;
    if (outBitOff == 0) {
        alignedBitHelper(outWords, outLsb / 8, inWords, inLsb, width);
        return;
    }
    uint32_t left = 8 - outBitOff;
    if (width > left)
        alignedBitHelper(outWords, (outLsb + left) / 8, inWords, inLsb + left, width - left);

    uint32_t outSize = sizeof(OutWordT);
    uint32_t outIndexOff = outLsb / 8 / outSize;
    uint32_t outByteOff = (outLsb / 8) % outSize;

    // Arithmetic operators in C++ don't accept operands smaller than
    // int(Integral promotion), so we can't do a shift on uint8_t directly.
    OutWordT outMask = (OutWordT(0xffU << outBitOff) & 0xffU) << (8 * outByteOff);

    uint32_t inSize = sizeof(InWordT);
    uint32_t inIndexOff = inLsb / 8 / inSize;
    uint32_t inByteOff = (inLsb / 8) % inSize;
    uint32_t inBitOff = inLsb % 8;

    uint8_t byte = uint8_t(inWords[inIndexOff] >> (8 * inByteOff)) >> inBitOff;
    uint32_t validBits = 8 - inBitOff;

    if (validBits >= left) {
        outWords[outIndexOff] = (outWords[outIndexOff] & ~outMask)
                                | ((OutWordT(byte) << (8 * outByteOff + outBitOff)) & outMask);
        return;
    }
    ++inByteOff;
    if (inByteOff == inSize) {
        inByteOff = 0;
        ++inIndexOff;
    }
    uint8_t newByte = uint8_t(inWords[inIndexOff] >> (8 * inByteOff));
    byte |= newByte << validBits;
    outWords[outIndexOff] = (outWords[outIndexOff] & ~outMask)
                            | ((OutWordT(byte) << (8 * outByteOff + outBitOff)) & outMask);
}

// 6 bits
union SUB_T {
    CData /*5:0*/ a;
    CData /*2:0*/ b;

    // Initailize unused bits with zero
    SUB_T() { a = 0; }

    CData get() const {
        CData __v;
        bitHelper(&__v, 0, &a, 0, 6);
        return __v;
    }
    void set(const CData& v) { bitHelper(&a, 0, &v, 0, 6); }
};

// 41 + 24 + 6 = 71 bits
struct IN_T {
    SUB_T /*5:0*/ c;
    CData /*5:0*/ b[4];
    QData /*40:0*/ a;

    IN_T() {
        a = 0;
        for (int i = 0; i < 4; ++i) { b[i] = 0; }
    }

    VlWide<3> get() {
        VlWide<3> __v{};
        CData data_c = c.get();
        bitHelper(__v.data(), 0, &data_c, 0, 6);
        for (int i = 0; i < 4; ++i) { bitHelper(__v.data(), 6 + i * 6, &b[i], 0, 6); }
        bitHelper(__v.data(), 30, &a, 0, 41);
        return __v;
    }

    void set(const VlWide<3>& __v) {
        CData data_c;
        bitHelper(&data_c, 0, __v.data(), 0, 6);
        c.set(data_c);
        for (int i = 0; i < 4; ++i) { bitHelper(&b[i], 0, __v.data(), 6 + i * 6, 6); }
        bitHelper(&a, 0, __v.data(), 30, 41);
    }
};

struct OUT_T {
    QData /*40:0*/ a;
    SUB_T /*5:0*/ c;
    CData /*5:0*/ b[4];

    // Initailize unused bits with zero
    OUT_T() {
        for (int i = 0; i < 4; ++i) { b[i] = 0; }
        a = 0;
    }

    VlWide<3> get() {
        VlWide<3> __v{};
        bitHelper(__v.data(), 0, &a, 0, 41);
        CData data_c = c.get();
        bitHelper(__v.data(), 41, &data_c, 0, 6);
        for (int i = 0; i < 4; ++i) { bitHelper(__v.data(), 47 + i * 6, &b[i], 0, 6); }
        return __v;
    }

    void set(const VlWide<3>& __v) {
        bitHelper(&a, 0, __v.data(), 0, 41);
        CData data_c;
        bitHelper(&data_c, 0, __v.data(), 41, 6);
        c.set(data_c);
        for (int i = 0; i < 4; ++i) { bitHelper(&b[i], 0, __v.data(), 47 + i * 6, 6); }
    }
};

int errors = 0;

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->randReset(2);
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> adder{new VM_PREFIX{contextp.get()}};

    {
        IN_T in1, in2;
        OUT_T out;
        in1.a = 0x12345678;  // 0b0001_0010_0011_0100_0101_0110_0111_1000
        in1.b[0] = 0x1;  // 0b000001
        in1.b[1] = 0x2;  // 0b000010
        in1.b[2] = 0x3;  // 0b000011
        in1.b[3] = 0x4;  // 0b000100
        in1.c.a = 0x5;  // 0b000101
        in2.a = 0x11111111;
        in2.b[0] = 0x10;
        in2.b[1] = 0x20;
        in2.b[2] = 0x30;
        in2.b[3] = 0x30;
        in2.c.a = 0x20;

        adder->op1 = in1.get();
        adder->op2 = in2.get();
        adder->eval();
        out.set(adder->out);

        TEST_CHECK_EQ(out.b[0], 0x11);
        TEST_CHECK_EQ(out.b[1], 0x22);
        TEST_CHECK_EQ(out.b[2], 0x33);
        TEST_CHECK_EQ(out.b[3], 0x34);
        TEST_CHECK_EQ(out.c.a, 0x25);
        TEST_CHECK_EQ(out.a, 0x23456789);
    }

    printf("*-* All Finished *-*\n");
    return errors;
}