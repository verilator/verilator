// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   parameter	UNSIZED = 10;

   integer cyc=1;
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==1) begin
	 if ({UNSIZED,UNSIZED+1} != {32'd10, 32'd11}) $stop;
	 if ({2{UNSIZED}} != {32'd10, 32'd10}) $stop;
      end
      if (cyc==9) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
