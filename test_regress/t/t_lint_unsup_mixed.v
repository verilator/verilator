// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2016 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t
   (
   input wire clk,
   input wire a,
   input wire b
   );

   integer q;

   // bug1120
   always @ (a or posedge clk)
     begin
	if (a)
          q = 0;
	else
          q = q + 1;
     end

   // bug934
   integer qb;
   always @((a && b) or posedge clk) begin
      if (a)
	qb = 0;
      else
	qb = qb + 1;
   end

endmodule
