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

module t (
   input clk,
   input dummy_clk // Never toggled from C++
);

   int count;

   logic [7:0] pub_byte /* verilator public_flat_rw */ = 123;
   logic [7:0] comb_byte;

   always_comb comb_byte = `IMPURE_ONE ? pub_byte : '0;

   always_ff @(posedge clk) begin
      count <= count + 1;
      if (comb_byte != pub_byte) begin
         $display("%%Error: comb_byte (%0d) != pub_byte (%0d)", comb_byte, pub_byte);
         $stop;
      end
      if (count == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   always_ff @(posedge dummy_clk) begin
      comb_byte = ~pub_byte;
   end
endmodule
