// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   o,
   // Inputs
   clk, i, idx
   );
   input clk;
   input [3:0] i;
   input idx;
   output [3:0] o;

   logic [1:0][3:0] array;

   always_comb array[0] = i;

   always @ (posedge clk)
     array[0] <= array[0];

   struct {
     logic [3:0] a;
     logic [3:0] b;
   } unpacked;

   always_comb unpacked.a = i;

   always @ (posedge clk)
     unpacked.b <= unpacked.a;

   assign o = array[idx] + unpacked.a;

endmodule
