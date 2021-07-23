// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;

   reg [89:0]	in;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [89:0] 		out;			// From test of Test.v
   wire [44:0] 		line0;
   wire [44:0] 		line1;
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .out			(out[89:0]),
	      .line0			(line0[44:0]),
	      .line1			(line1[44:0]),
	      // Inputs
	      .clk			(clk),
	      .in			(in[89:0]));

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d in=%x out=%x\n",$time, cyc, in, out);
`endif
      cyc <= cyc + 1;
      if (cyc==0) begin
	 // Setup
	 in <= 90'h3FFFFFFFFFFFFFFFFFFFFFF;
      end
      else if (cyc==10) begin
         if (in==out) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
	 else begin
	   $write("*-* Failed!! *-*\n");
	    $finish;
	 end
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   line0, line1, out,
   // Inputs
   clk, in
   );

   input clk;
   input [89:0] in;

   output reg [44:0]	line0;
   output reg [44:0]	line1;
   output reg [89:0]	out;

   assign  {line0,line1} = in;
   always @(posedge clk) begin
      out <= {line0,line1};
   end
endmodule
