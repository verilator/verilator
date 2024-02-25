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

// struct in1_t should cover parts of VL_ASSIGNSEL_II functions
typedef struct packed {
  logic [3:0]  a;
  logic [11:0] b;
} in1_t;  // 4 + 12 = 16

typedef struct packed {
  logic [11:0] b;
  logic [3:0]  a;
} out1_t;

// struct in2_t should cover all VL_ASSIGNSEL_II functions
typedef struct packed {
  logic [2:0]  a;
  logic [8:0]  b;
  logic [18:0] c;
} in2_t;  // 3 + 9 + 19 = 31

typedef struct packed {
  logic [8:0]  b;
  logic [18:0] c;
  logic [2:0]  a;
} out2_t;

// struct in3_t should cover all VL_ASSIGNSEL_XQ functions
typedef struct packed {
  logic [1:0]  a;
  logic [8:0]  b;
  logic [16:0] c;
  logic [32:0] d;
} in3_t;  // 33 + 17 + 9 + 2 = 61

typedef struct packed {
  logic [8:0]  b;
  logic [1:0]  a;
  logic [32:0] d;
  logic [16:0] c;
} out3_t;

// struct in4_t should cover all VL_ASSIGNSEL_XW functions
typedef struct packed {
  logic [4:0]  a;
  logic [12:0] b;
  logic [24:0] c;
  logic [48:0] d;
  logic [80:0] e;
} in4_t;  // 5 + 13 + 25 + 49 + 81 = 173

typedef struct packed {
  logic [24:0] c;
  logic [48:0] d;
  logic [80:0] e;
  logic [4:0]  a;
  logic [12:0] b;
} out4_t;
*/

#define CONCAT_IMPL(a, b) a##b
#define CONCAT(a, b) CONCAT_IMPL(a, b)
#define CONCAT5(a, b, c, d, e) CONCAT(CONCAT(CONCAT(CONCAT(a, b), c), d), e)
#define EXPORTED_STRUCT_NAME(STRUCT_NAME, NUMBER) \
    CONCAT5(VM_PREFIX, _, STRUCT_NAME, __struct__, NUMBER)
#define EXPORTED_UNION_NAME(UNION_NAME, NUMBER) \
    CONCAT5(VM_PREFIX, _, UNION_NAME, __union__, NUMBER)
#define SUB_T EXPORTED_UNION_NAME(sub_t, 0)
#define IN_T EXPORTED_STRUCT_NAME(in_t, 0)
#define OUT_T EXPORTED_STRUCT_NAME(out_t, 0)

#define IN1_T EXPORTED_STRUCT_NAME(in1_t, 0)
#define IN2_T EXPORTED_STRUCT_NAME(in2_t, 0)
#define IN3_T EXPORTED_STRUCT_NAME(in3_t, 0)
#define IN4_T EXPORTED_STRUCT_NAME(in4_t, 0)
#define OUT1_T EXPORTED_STRUCT_NAME(out1_t, 0)
#define OUT2_T EXPORTED_STRUCT_NAME(out2_t, 0)
#define OUT3_T EXPORTED_STRUCT_NAME(out3_t, 0)
#define OUT4_T EXPORTED_STRUCT_NAME(out4_t, 0)

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
        in1.a = 0x12345678;
        in1.__SYM__nullptr[0] = 0x1;
        in1.__SYM__nullptr[1] = 0x2;
        in1.__SYM__nullptr[2] = 0x3;
        in1.__SYM__nullptr[3] = 0x4;
        in1.get__0.a = 0x5;
        in2.a = 0x11111111;
        in2.__SYM__nullptr[0] = 0x10;
        in2.__SYM__nullptr[1] = 0x20;
        in2.__SYM__nullptr[2] = 0x30;
        in2.__SYM__nullptr[3] = 0x30;
        in2.get__0.a = 0x20;

        adder->op1 = in1.get();
        adder->op2 = in2.get();
        adder->eval();
        out.set(adder->out);

        TEST_CHECK_EQ(out.__SYM__nullptr[0], 0x11);
        TEST_CHECK_EQ(out.__SYM__nullptr[1], 0x22);
        TEST_CHECK_EQ(out.__SYM__nullptr[2], 0x33);
        TEST_CHECK_EQ(out.__SYM__nullptr[3], 0x34);
        TEST_CHECK_EQ(out.get__0.a, 0x25);
        TEST_CHECK_EQ(out.a, 0x23456789);

        // Additional tests
        IN1_T op1a, op1b;
        OUT1_T out1;

        op1a.a = 0x4;
        op1b.a = 0x5;
        op1a.b = 0x1fe;
        op1b.b = 0x1ef;

        adder->op1a = op1a.get();
        adder->op1b = op1b.get();
        adder->eval();
        out1.set(adder->out1);

        TEST_CHECK_EQ(out1.a, op1a.a + op1b.a);
        TEST_CHECK_EQ(out1.b, op1a.b + op1b.b);

        IN2_T op2a, op2b;
        OUT2_T out2;

        op2a.a = 0x4;
        op2b.a = 0x3;
        op2a.b = 0xff;
        op2b.b = 0x1;
        op2a.c = 0x11212;
        op2b.c = 0x12121;

        adder->op2a = op2a.get();
        adder->op2b = op2b.get();
        adder->eval();
        out2.set(adder->out2);

        TEST_CHECK_EQ(out2.a, op2a.a + op2b.a);
        TEST_CHECK_EQ(out2.b, op2a.b + op2b.b);
        TEST_CHECK_EQ(out2.c, op2a.c + op2b.c);

        IN3_T op3a, op3b;
        OUT3_T out3;

        op3a.a = 0x1;
        op3b.a = 0x2;
        op3a.b = 0x155;
        op3b.b = 0x44;
        op3a.c = 0xff;
        op3b.c = 0xff00;
        op3a.d = 0x123232323ULL;
        op3b.d = 0x32323232ULL;

        adder->op3a = op3a.get();
        adder->op3b = op3b.get();
        adder->eval();
        out3.set(adder->out3);

        TEST_CHECK_EQ(out3.a, op3a.a + op3b.a);
        TEST_CHECK_EQ(out3.b, op3a.b + op3b.b);
        TEST_CHECK_EQ(out3.c, op3a.c + op3b.c);
        TEST_CHECK_EQ(out3.d, op3a.d + op3b.d);

        IN4_T op4a, op4b;
        OUT4_T out4;

        op4a.a = 0xf;
        op4b.a = 0x2;
        op4a.b = 0x123;
        op4b.b = 0x432;
        op4a.c = 0x123456;
        op4b.c = 0x654321;
        op4a.d = 0x123456789ULL;
        op4b.d = 0x987654321ULL;
        op4a.e[0] = 0x12345678;
        op4b.e[0] = 0x87654321;
        op4a.e[1] = 0xabcde000;
        op4b.e[1] = 0x000cdeba;
        op4a.e[2] = 0xe;
        op4b.e[2] = 0xf;

        adder->op4a = op4a.get();
        adder->op4b = op4b.get();
        adder->eval();
        out4.set(adder->out4);

        TEST_CHECK_EQ(out4.a, op4a.a + op4b.a);
        TEST_CHECK_EQ(out4.b, op4a.b + op4b.b);
        TEST_CHECK_EQ(out4.c, op4a.c + op4b.c);
        TEST_CHECK_EQ(out4.d, op4a.d + op4b.d);
        TEST_CHECK_EQ(out4.e[0], op4a.e[0] + op4b.e[0]);
        TEST_CHECK_EQ(out4.e[1], op4a.e[1] + op4b.e[1]);
        TEST_CHECK_EQ(out4.e[2], op4a.e[2] + op4b.e[2]);
    }

    printf("*-* All Finished *-*\n");
    return errors;
}
