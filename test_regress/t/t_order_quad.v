// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

//bug 762
module t(a0, y);
   input [3:0] a0;
   output [44:0] y;

   assign y[40] = 0;
   assign y[30] = 0;
   // verilator lint_off UNOPTFLAT
   assign { y[44:41], y[39:31], y[29:0] } = { 6'b000000, a0, 7'b0000000, y[40], y[30], y[30], y[30], y[30], 21'b000000000000000000000 };

endmodule
