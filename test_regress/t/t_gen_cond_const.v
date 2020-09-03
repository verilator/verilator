// DESCRIPTION: Verilator: Verilog Test for generate IF constants
//
// The given generate loop should have a constant expression as argument. This
// test checks it really does evaluate as constant.

// This file ONLY is placed into the Public Domain, for any use, without
// warranty, 2012 by Jeremy Bennett.
// SPDX-License-Identifier: CC0-1.0


`define MAX_SIZE  4


module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // Set the parameters, so that we use a size less than MAX_SIZE
   test_gen
     #(.SIZE (2),
       .MASK (4'b1111))
     i_test_gen (.clk (clk));

   // This is only a compilation test, but for good measure we do one clock
   // cycle.
   integer count;

   initial begin
      count = 0;
   end

   always @(posedge clk) begin
      if (count == 1) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
      else begin
	 count = count + 1;
      end
   end

endmodule // t


module test_gen

  #( parameter
     SIZE = `MAX_SIZE,
     MASK = `MAX_SIZE'b0)

 (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // Generate blocks that rely on short-circuiting of the logic to avoid
   // errors.
   generate
      if ((SIZE < 8'h04) && MASK[0]) begin
	 always @(posedge clk) begin
`ifdef TEST_VERBOSE
	    $write ("Generate IF MASK[0] = %d\n", MASK[0]);
`endif
	 end
      end
   endgenerate

endmodule
