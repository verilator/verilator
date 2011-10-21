// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   parameter PAR = 3;

   input clk;
   integer cyc=1;

   reg [31:0] dly0;
   wire [31:0] dly1;
   wire [31:0] dly2 = dly1 + 32'h1;

   assign #(1.2000000000000000) dly1 = dly0 + 32'h1;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==1) begin
	 dly0 <= #0 32'h11;
      end
      else if (cyc==2) begin
	 dly0 <= #0.12 dly0 + 32'h12;
      end
      else if (cyc==3) begin
	 if (dly0 !== 32'h23) $stop;
	 if (dly2 !== 32'h25) $stop;
	 $write("*-* All Finished *-*\n");
	 #100 $finish;
      end
   end

endmodule
