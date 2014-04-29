// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

`timescale 1 ns/ 1ns

module top (/*AUTOARG*/
   // Outputs
   passed, out_small, out_quad, out_wide,
   // Inputs
   clk, fastclk, reset_l, in_small, in_quad, in_wide
   );

   output passed;
   input  clk;
   input  fastclk;
   input  reset_l;

   output [1:0] out_small;
   output [39:0] out_quad;
   output [69:0] out_wide;
   input [1:0] 	 in_small;
   input [39:0]  in_quad;
   input [69:0]  in_wide;

   wire [1:0] 	 out_small = in_small | {2{reset_l}};
   wire [39:0] 	 out_quad = in_quad | {40{reset_l}};
   wire [69:0] 	 out_wide = in_wide | {70{reset_l}};

   initial begin
      $write("Hello World!\n");
   end

   // Example sub module
   t t (/*AUTOINST*/
	// Outputs
	.passed				(passed),
	// Inputs
	.clk				(clk),
	.fastclk			(fastclk),
	.reset_l			(reset_l));

endmodule
