// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t();
    parameter LEN1 = 8;
    test #(
        .LEN(LEN1),
        .LST('{LEN1{0}})
    )
    inst1();

    parameter LEN2 = 3;
    test #(
        .LEN(LEN2*2),
        .LST('{LEN2*2{0}})
    )
    inst2();

    test #(
        .LEN(LEN1 + LEN2),
        .LST('{(LEN1+LEN2){0}})
    )
    inst3();

    test #(
        .LEN(LEN1 + LEN2),
        .LST('{LEN1{0}, LEN2{1}})
    )
    inst4();
endmodule

module test #(
    parameter LEN = 4,
    parameter LST[LEN] = '{LEN{0}}
)();
endmodule
