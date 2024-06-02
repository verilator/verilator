// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   int a;
   reg [3:0] b;

   initial begin
      a = 1;
      b = (-1)'(a);  // Bad
   end

endmodule
