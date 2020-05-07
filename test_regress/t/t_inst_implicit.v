// DESCRIPTION:tor:ilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2015 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire [31:0] o;
   wire [31:0] oe;

   Test test (/*AUTOINST*/
	      // Outputs
	      .o			(o[31:0]),
	      .oe			(oe[31:0]));

   // Test loop
   always @ (posedge clk) begin
      if (o  !== 32'h00000001) $stop;
      if (oe !== 32'h00000001) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module subimp(o,oe);
   output [31:0] o;
   assign o = 32'h12345679;
   output [31:0] oe;
   assign oe = 32'hab345679;
endmodule

module Test(o,oe);
   output [31:0] o;
   output [31:0] oe;
   wire [31:0] 	 xe;
   assign xe[31:1] = 0;
   // verilator lint_off IMPLICIT
   // verilator lint_off WIDTH
   subimp subimp(x,	 // x is implicit and one bit
		 xe[0]); // xe explicit one bit
   assign o = x;
   assign oe = xe;
   // verilator lint_on WIDTH
   // verilator lint_on IMPLICIT
endmodule
