// DESCRIPTION: Verilator: Simple test of unoptflat
//
// Simple demonstration of an UNOPTFLAT combinatorial loop, using just 2 bits.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Jeremy Bennett.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire [1:0] x = { x[0], clk };

   initial begin
      x = 0;
   end

   always @(posedge clk or negedge clk) begin

`ifdef TEST_VERBOSE
      $write("x = %x\n", x);
`endif

      if (x[1] != 0) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
