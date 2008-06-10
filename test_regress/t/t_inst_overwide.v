// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   outc_w30, outd_w73,
   // Inputs
   clk, ina_w1, inb_w61
   );

   input clk;

   input         ina_w1;
   input  [60:0] inb_w61;
   output [29:0] outc_w30;
   output [72:0] outd_w73;

   sub sub (
	    // Outputs
	    .outy_w92	(outc_w30),	// .large => (small)
	    .outz_w22	(outd_w73),	// .small => (large)
	    // Inputs
	    .clk	(clk),
	    .inw_w31	(ina_w1),	// .large <= (small)
	    .inx_w11	(inb_w61)	// .small <= (large)
	    );

endmodule

module sub (/*AUTOARG*/
   // Outputs
   outy_w92, outz_w22,
   // Inputs
   clk, inw_w31, inx_w11
   );

   input 	clk;
   input [30:0]	inw_w31;
   input [10:0]	inx_w11;
   output reg [91:0] outy_w92  /*verilator public*/;
   output reg [21:0] outz_w22  /*verilator public*/;

   always @(posedge clk) begin
      outy_w92 <= {inw_w31[29:0],inw_w31[29:0],inw_w31[29:0],2'b00};
      outz_w22 <= {inx_w11[10:0],inx_w11[10:0]};
   end

endmodule // regfile
