// DESCRIPTION: Verilator: Verilog Test for short-circuiting in generate "if"
// that should not work.
//
// The given generate loops should attempt to access invalid bits of mask and
// trigger errors.
// is defined by SIZE. However since the loop range is larger, this only works
// if short-circuited evaluation of the generate loop is in place.

// This file ONLY is placed into the Public Domain, for any use, without
// warranty, 2012 by Jeremy Bennett.
// SPDX-License-Identifier: CC0-1.0

`define MAX_SIZE  3


module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // Set the parameters, so that we use a size less than MAX_SIZE
   test_gen
     #(.SIZE (2),
       .MASK (2'b11))
     i_test_gen (.clk (clk));

   // This is only a compilation test, so we can immediately finish
   always @(posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
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

   // Generate blocks that all have errors in applying short-circuting to
   // generate "if" conditionals.

   // Attempt to access invalid bits of MASK in different ways
   generate
      genvar g;

      for (g = 0; g < `MAX_SIZE; g = g + 1) begin
         if ((g < (SIZE + 1)) && MASK[g]) begin
            always @(posedge clk) begin
`ifdef TEST_VERBOSE
               $write ("Logical AND generate if MASK [%1d] = %d\n", g, MASK[g]);
`endif
            end
         end
      end
   endgenerate

   generate
      for (g = 0; g < `MAX_SIZE; g = g + 1) begin
         if ((g < SIZE) && MASK[g + 1]) begin
            always @(posedge clk) begin
`ifdef TEST_VERBOSE
               $write ("Logical AND generate if MASK [%1d] = %d\n", g, MASK[g]);
`endif
            end
         end
      end
   endgenerate

   // Attempt to short-circuit bitwise AND
   generate
      for (g = 0; g < `MAX_SIZE; g = g + 1) begin
         if ((g < (SIZE)) & MASK[g]) begin
            always @(posedge clk) begin
`ifdef TEST_VERBOSE
               $write ("Bitwise AND generate if MASK [%1d] = %d\n", g, MASK[g]);
`endif
            end
         end
      end
   endgenerate

   // Attempt to short-circuit bitwise OR
   generate
      for (g = 0; g < `MAX_SIZE; g = g + 1) begin
         if (!((g >= SIZE) | ~MASK[g])) begin
            always @(posedge clk) begin
`ifdef TEST_VERBOSE
               $write ("Bitwise OR generate if MASK [%1d] = %d\n", g, MASK[g]);
`endif
            end
         end
      end
   endgenerate

endmodule
