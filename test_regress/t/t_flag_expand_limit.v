// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// issue3005

module t #(parameter NV = 2000)
   (
    input          a,
    input          w1,
    input [127:0]  w2,
    output [ 31:0] o,

    input [319:0]  bi,
    output [319:0]  bo
    );

   // verilator lint_off WIDTH
   wire [NV-1:0]   d = a ? NV'(0) : {NV{w2}};
   // verilator lint_on WIDTH
   assign        o = d[31:0];

   assign bo = ~bi;

endmodule
