// DESCRIPTION: Verilator: Simple test of unoptflat
//
// Simple demonstration of an UNOPTFLAT combinatorial loop, using just 2 bits.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 Jeremy Bennett
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire [1:0] x = { x[0], clk };

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
