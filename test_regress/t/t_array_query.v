// DESCRIPTION: Verilator: System Verilog test of array querying functions.
//
// This code instantiates a module that calls the various array querying
// functions.
//
// This file ONLY is placed into the Public Domain, for any use, without
// warranty.
// SPDX-License-Identifier: CC0-1.0

// Contributed 2012 by Jeremy Bennett, Embecosm.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire  a = clk;
   wire  b = 1'b0;
   reg   c;

   array_test array_test_i (/*AUTOINST*/
			    // Inputs
			    .clk		(clk));

endmodule


// Check the array sizing functions work correctly.
module array_test

  #( parameter
     LEFT  = 5,
     RIGHT = 55)

 (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // verilator lint_off LITENDIAN
   reg [7:0] a [LEFT:RIGHT];
   // verilator lint_on LITENDIAN

   typedef reg [7:0] r_t;

   integer   l;
   integer   r;
   integer   s;

   always @(posedge clk) begin
      l = $left (a);
      r = $right (a);
      s = $size (a);

`ifdef TEST_VERBOSE
      $write ("$left (a) = %d, $right (a) = %d, $size (a) = %d\n", l, r, s);
`endif

      if ((l != LEFT) || (r != RIGHT) || (s != (RIGHT - LEFT + 1))) $stop;
      if ($left(r_t)!=7 || $right(r_t)!=0 || $size(r_t)!=8 || $bits(r_t) !=8) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
