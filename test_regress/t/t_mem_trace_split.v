// DESCRIPTION: Verilator: Demonstrate complex user typea problem with --x-assign
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   logic [31:0] mem_a [32];
   logic [15:0] mem_b [32];

   int cyc = 0;

   // finish report
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      mem_a[cyc] <= cyc;
      mem_b[cyc] <= 16'(cyc);
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end


endmodule
