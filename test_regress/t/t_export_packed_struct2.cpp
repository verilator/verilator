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

#include <ios>
#include <iostream>

#include VM_PREFIX_INCLUDE
#include VM_PREFIX_ROOT_INCLUDE

#include "TestCheck.h"
#include "Vt_export_packed_struct2___024unit__03a__03acls_in__Vclpkg.h"

/*
// Packed struct in package
package TEST_TYPES;
  typedef union packed {
    logic [64:0] a;
    logic [2:0]  b;
  } sub_t;
  typedef struct packed {
    struct packed {  // Anonymous packed struct
      logic a;
    } anon;
    TEST_TYPES::sub_t [2:0][2:0][2:0] b;
  } in_t;
  typedef struct packed {
    TEST_TYPES::sub_t [2:0][2:0][2:0] b;
    struct packed {logic a;} anon;
  } out_t;
endpackage

// Packed struct in class
class cls_in;
  typedef struct packed {
    logic a;
    TEST_TYPES::sub_t [2:0][2:0][2:0] b;
  } in_t;
  in_t in;
endclass  //cls
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
#define IN2_T EXPORTED_STRUCT_NAME(in_t, 1)
#define OUT_T EXPORTED_STRUCT_NAME(out_t, 0)

int errors = 0;

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->randReset(2);
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> adder{new VM_PREFIX{contextp.get()}};

    {
        IN_T in;
        IN2_T tmp;
        OUT_T out;
        for (int i = 0; i < 3; ++i) {
            for (int j = 0; j < 3; ++j) {
                for (int k = 0; k < 3; ++k) {
                    VL_SET_WQ(in.b[i][j][k].a, 0x1234123412341234UL);
                    // Set last bit zero and upper bits one
                    in.b[i][j][k].a[2] = 0xfe;
                }
            }
        }
        in.anon.a = 0x1;

        adder->op1 = in.get();
        adder->eval();
        out.set(adder->out);

        std::memset(reinterpret_cast<void*>(&tmp), 0xff, sizeof(tmp));
        // `set` function should clear upper bits of `tmp.a`
        tmp.set(adder->rootp->add__DOT__op2->__PVT__in);

        for (int i = 0; i < 3; ++i) {
            for (int j = 0; j < 3; ++j) {
                for (int k = 0; k < 3; ++k) {
                    TEST_CHECK_EQ(tmp.b[i][j][k].a[0], 0x12341234);
                    TEST_CHECK_EQ(tmp.b[i][j][k].a[1], 0x12341234);
                    TEST_CHECK_EQ(tmp.b[i][j][k].a[2], 0);
                }
            }
        }
        TEST_CHECK_EQ(tmp.a, 0x1);

        for (int i = 0; i < 3; ++i) {
            for (int j = 0; j < 3; ++j) {
                for (int k = 0; k < 3; ++k) {
                    TEST_CHECK_EQ(out.b[i][j][k].a[0], 0x24682468);
                    TEST_CHECK_EQ(out.b[i][j][k].a[1], 0x24682468);
                    TEST_CHECK_EQ(out.b[i][j][k].a[2], 0x0);
                }
            }
        }
        TEST_CHECK_EQ(out.anon.a, 0x0);
    }

    printf("*-* All Finished *-*\n");
    return errors;
}
