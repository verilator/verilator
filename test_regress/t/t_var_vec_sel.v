// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// bug601

module t (
   input       clk,
   input [3:0] in3, // worky
   input [0:0] in2 [3:0], // worky
   input       in1 [3:0], // no worky
   input [1:0] sel,
   output reg  out1,
   output reg  out2,
   output reg  out3
   );

   always @(posedge clk) begin
      out3 <= in3[sel] ? in3[sel] : out3;
      out2 <= in2[sel] ? in2[sel] : out2;
      out1 <= in1[sel] ? in1[sel] : out1; // breaks
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
