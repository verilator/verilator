// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   a, y
   );

   input [1:0] a;
   output [3:0] y;

   Test #(.C(2))
      test (.*);
endmodule

module Test
  #(C = 3,
    localparam O = 1 << C)
   (input [C-1:0] a,
    output reg [O-1:0] y);
   initial begin
      if (O != 4) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
