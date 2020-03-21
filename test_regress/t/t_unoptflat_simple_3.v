// DESCRIPTION: Verilator: Simple test of unoptflat
//
// Demonstration of an UNOPTFLAT combinatorial loop using 3 bits and looping
// through 2 sub-modules.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Jeremy Bennett.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire [2:0] x;

   initial begin
      x = 3'b000;
   end

   test1 test1i ( .clk     (clk),
		  .xvecin  (x[1:0]),
		  .xvecout (x[2:1]));

   test2 test2i ( .clk     (clk),
		  .xvecin  (x[2:1]),
		  .xvecout (x[1:0]));

   always @(posedge clk or negedge clk) begin

`ifdef TEST_VERBOSE
      $write("x = %x\n", x);
`endif

      if (x[1] != 0) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule // t


module test1
  (/*AUTOARG*/
   // Inputs
   clk,
   xvecin,
   // Outputs
   xvecout
   );

   input clk;
   input wire [1:0] xvecin;

   output wire [1:0] xvecout;

   assign xvecout = {xvecin[0], clk};

endmodule // test


module test2
  (/*AUTOARG*/
   // Inputs
   clk,
   xvecin,
   // Outputs
   xvecout
   );

   input clk;
   input wire [1:0] xvecin;

   output wire [1:0] xvecout;

   assign xvecout = {clk, xvecin[1]};

endmodule // test
