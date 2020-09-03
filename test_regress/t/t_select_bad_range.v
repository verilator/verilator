// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   reg [43:0] mi;
   reg        sel;
   reg [3:0]  sel2;

   always @ (posedge clk) begin
      mi = 44'h123;
      sel = mi[44];
      sel2 = mi[44:41];
      $write ("Bad select %x %x\n", sel, sel2);
   end
endmodule
