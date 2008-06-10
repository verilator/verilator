// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2006 by Wilson Snyder.

module t (clk);

   sub sub ();

   input clk;
   integer cyc=1;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==2) begin
	 // Not $finish; as we don't want a message to scroll by
	 $c("Verilated::gotFinish(true);");
      end
   end
endmodule

module sub;
   /* verilator public_module */
endmodule
