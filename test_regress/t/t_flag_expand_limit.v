// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2021 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// issue3005

module t #(parameter NV = 2000)
   (
    input          a,
    input          w1,
    input [127:0]  w2,
    output [ 31:0] o,

    input [319:0]  bi,
    output [319:0]  bo,

    input [319:0]  c_i1,
    input [319:0]  c_i2,
    output         c_eq_o,
    output         c_neq_o,

    input [319:0]  d_red_i,
    output         d_red_and_o,
    output         d_red_or_o,
    output         d_red_xor_o
    );

   // verilator lint_off WIDTH
   wire [NV-1:0]   d = a ? NV'(0) : {NV{w2}};
   // verilator lint_on WIDTH
   assign        o = d[31:0];

   assign bo = ~bi;

   assign c_eq_o  = c_i1 == c_i2;
   assign c_neq_o = c_i1 != c_i2;

   assign d_red_and_o = &d_red_i;
   assign d_red_or_o  = |d_red_i;
   assign d_red_xor_o = ^d_red_i;

endmodule
