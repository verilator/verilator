// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   q,
   // Inputs
   clk, d
   );
   input clk;
   input d;
   output wire [1:0] q;

   // This demonstrates how warning disables should be propagated across module boundaries.

   m1 m1 (/*AUTOINST*/
	  // Outputs
	  .q				(q[1:0]),
	  // Inputs
	  .clk				(clk),
	  .d				(d));
endmodule

module m1
  (
   input clk,
   input d,
   output wire [1:0] q
   );
   
   m2 m2 (/*AUTOINST*/
	  // Outputs
	  .q				(q[1:0]),
	  // Inputs
	  .clk				(clk),
	  .d				(d));
endmodule

module m2
  (
   input clk,
   input d,
   // Due to bug the below disable used to be ignored.
   // verilator lint_off UNOPT
   output reg [1:0] q
   // verilator lint_on UNOPT
   );
   
   always @* begin
      q[1] = d;
   end

   always @* begin
      q[0] = q[1];
   end

endmodule
