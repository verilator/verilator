// DESCRIPTION: Verilator: public clock signal
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2022 by Todd Strader
// SPDX-License-Identifier: CC0-1.0

`ifdef VERILATOR
// The '$c1(1)' is there to prevent inlining of the signal by V3Gate
`define IMPURE_ONE ($c(1))
`else
// Use standard $random (chaces of getting 2 consecutive zeroes is zero).
`define IMPURE_ONE (|($random | $random))
`endif

module t ();

   logic clk /* verilator public_flat_rw */;
   int count;
   wire other_clk = `IMPURE_ONE & clk;

   always_ff @(posedge other_clk) begin
      count <= count + 1;
      if (count == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
