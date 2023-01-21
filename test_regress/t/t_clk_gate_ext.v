// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg   clk_en = 1'b0;
   wire  clk_gated = clk & clk_en;
   wire [1:0] clks = {1'b0, clk_gated};

   always @(posedge clks[0]) begin
      $display("ERROR: clks[0] should not be active!");
      $stop;
   end

   int cyc = 0;
   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
