// DESCRIPTION: Verilator: public clock signal
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2021 by Todd Strader
// SPDX-License-Identifier: CC0-1.0

module t ();

   logic clk /* verilator public_flat_rw */;
   int count;
   logic other_clk /* verilator public_flat_rw */;

   always_comb other_clk = clk;

   always_ff @(posedge other_clk) begin
      count <= count + 1;
      if (count == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
