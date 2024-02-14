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
    }

    printf("*-* All Finished *-*\n");
    return errors;
}
