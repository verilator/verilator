// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk, unk, nonconst, mi
   );
   input clk;
   input unk;
   input nonconst;

   input [45:40] mi;
   reg [3:0]  sel2;
   reg [1<<29 : 0] hugerange;

   always @ (posedge clk) begin
      sel2 = mi[44 +: -1];
      sel2 = mi[44 +: 1<<29];
      sel2 = mi[44 +: nonconst];
      sel2 = mi[nonconst];
      sel2 = mi[nonconst : nonconst];
      sel2 = mi[1<<29 : 0];
   end
endmodule
