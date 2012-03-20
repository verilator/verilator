// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   q,
   // Inputs
   clk, d
   );
   input clk;
   input [3:0] d;
   output wire [3:0] q;

   logic [3:0] 	     between;

   mod1 cell1 (.q(between),
	       /*AUTOINST*/
	       // Inputs
	       .clk			(clk),
	       .d			(d[3:0]));

   mod2 cell2 (.d(between),
	       /*AUTOINST*/
	       // Outputs
	       .q			(q[3:0]),
	       // Inputs
	       .clk			(clk));

endmodule

module mod1
  (
   input clk,
   input [3:0] d,
   output logic [3:0] q
   );
   always @(posedge clk)
     q <= d;

endmodule

module mod2
  (
   input clk,
   input [3:0] d,
   output wire [3:0] q
   );

   assign q = d;

endmodule
