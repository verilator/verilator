// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [31:0] count;

   always @(posedge clk) begin
      count <= count + 1;
      if (count == 10) begin
         $write("*-* All Coverage *-*\n");
         $finish;
      end
   end
endmodule
