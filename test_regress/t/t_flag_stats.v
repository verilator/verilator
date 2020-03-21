// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (b);
   output reg [31:0] b;
   initial begin
      b = 22;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
