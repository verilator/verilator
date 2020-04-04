// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [65:0] idx /*verilator public*/; initial idx = 1;

   always @(posedge clk) begin
      case(idx)
	1: idx = 100;
	100: begin
	   $write("*-* All Finished *-*\n");
	   $finish;
	end
	default: $stop;
      endcase
   end

endmodule
