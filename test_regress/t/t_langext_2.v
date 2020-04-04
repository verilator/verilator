// DESCRIPTION: Verilator: Verilog Test module
//
// A test of the +1364-1995ext+ and +systemverilogext+ flags.
//
// This source code contains constructs that are valid in SystemVerilog 2009
// but not in Verilog 1995. So it should fail if we set the language to be
// Verilog 1995, but not SystemVerilog 2009.
//
// Compile only test, so no need for "All Finished" output.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Jeremy Bennett.
// SPDX-License-Identifier: CC0-1.0

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

   // This is a SystemVerilog 2009 only test
   generate
      genvar i;
      for (i=0; i<2; i=i+1) begin
	 always @(posedge clk) begin
	    unique0 case (i)
		      0: res[0:0] <= in;
		      1: res[1:1] <= in;
		    endcase
	 end
      end
   endgenerate
endmodule
