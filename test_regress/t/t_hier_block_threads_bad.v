// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   generate
      for (genvar i = 0; i < 2; ++i) Core hierCore(clk);
   endgenerate

   always @(negedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module Core(input clk); /* verilator hier_block */
   generate
      for (genvar i = 0; i < 2; ++i) SubCore sub(clk);
   endgenerate
   always @(posedge clk) $display("%m");
endmodule

module SubCore(input clk); /* verilator hier_block */
   always @(posedge clk) $display("%m");
endmodule
