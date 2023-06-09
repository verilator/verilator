// DESCRIPTION: Verilator: Test of Verilog and SystemVerilog integer literal differences
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Ethan Sifferman.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

    // "unbased_unsized_literal" is SystemVerilog only
    // Should fail with "NEWERSTD"
    wire [127:0] FOO1 = '0;
    wire [127:0] FOO2 = '1;
    wire [127:0] FOO3 = 'x;
    wire [127:0] FOO4 = 'X;
    wire [127:0] FOO5 = 'z;
    wire [127:0] FOO6 = 'Z;

endmodule
