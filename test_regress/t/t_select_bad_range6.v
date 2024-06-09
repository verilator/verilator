// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   logic [11:0] i;
   logic [30:0] o;

   assign o = i[31:1];

   always @(posedge clk) begin
      i = 12'h123;
   end
   always @(negedge clk) begin
      $write ("Bad select %x\n", o);
   end
endmodule
