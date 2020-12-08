// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   o,
   // Inputs
   clk, i
   );
   input clk;
   input [3:0] i;
   output [3:0] o;

   logic [1:0][3:0] array;

   always_comb array[0] = i;

   always @ (posedge clk)
     array[1] <= array[0];

   assign o = array[1];

endmodule
