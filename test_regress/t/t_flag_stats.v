// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (b, b2);
   output reg [31:0] b;
   output reg [31:0] b2;  // Need 2 vars of same width to cover V3Stats
   initial begin
      b = 11;
      b2 = 22;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
