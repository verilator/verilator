// DESCRIPTION: Verilator: public clock signal
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2021 by Anshul Shah
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;
   int count_1;
   int count_2;
   logic clk_1[0:1] /* verilator public_flat_rw */;
   logic clk_2[0:1] /* verilator public_flat_rw */;
   logic clk_3[0:1];

   always_comb clk_1[0] = ~clk;
   always_comb clk_2[0] = ~clk_1[0];
   always_comb clk_2[1] = ~clk_1[1];
   always_comb clk_3[0] = ~clk_2[0];
   always_comb clk_3[1] = ~clk_2[1];

   always_ff @(posedge clk_3[0]) begin
      count_1 <= count_1 + 1;
      if (count_1 >= 10 && count_2 >= 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   always_ff @(posedge clk_3[1]) begin
      count_2 <= count_2 + 1;
   end
endmodule
