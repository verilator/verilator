// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);

   sub sub ();

   input clk;
   integer cyc=1;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==2) begin
	 // Not $finish; as we don't want a message to scroll by
	 $c("Verilated::threadContextp()->gotFinish(true);");
      end
   end
endmodule

module sub;
   /* verilator public_module */
endmodule
