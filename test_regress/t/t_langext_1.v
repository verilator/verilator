// DESCRIPTION: Verilator: Verilog Test module
//
// A test of the +verilog1995ext+ and +verilog2001ext+ flags.
//
// This source code contains constructs that are valid in Verilog 2001 and
// SystemVerilog 2005/2009, but not in Verilog 1995. So it should fail if we
// set the language to be 1995, but not 2001.
//
// Compile only test, so no need for "All Finished" output.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Jeremy Bennett.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [1:0] 	res;

   // Instantiate the test
   test test_i (/*AUTOINST*/
	      // Outputs
	      .res			(res),
	      // Inputs
	      .clk			(clk),
	      .in			(1'b1));

endmodule

module test (// Outputs
	     res,
	     // Inputs
	     clk,
	     in
   );
   output [1:0]  res;
   input 	 clk;
   input 	 in;

   // This is a Verilog 2001 test
   generate
      genvar i;
      for (i=0; i<2; i=i+1) begin
	 always @(posedge clk) begin
	    res[i:i] <= in;
	 end
      end
   endgenerate
endmodule
