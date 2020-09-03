// DESCRIPTION: Verilator: Test for using DPI as general accessors
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.
// SPDX-License-Identifier: CC0-1.0
//
// Contributed by Jeremy Bennett and Jie Xul
//
// This test exercises the use of DPI to access signals and registers in a
// module hierarchy in a uniform fashion. See the discussion at
//
// https://www.veripool.org/boards/3/topics/show/752-Verilator-Command-line-specification-of-public-access-to-variables
//
// We need to test read and write access to:
// - scalars
// - vectors
// - array elements
// - slices of vectors or array elements
//
// We need to test that writing to non-writable elements generates an error.
//
// This Verilog would run forever. It will be stopped externally by the C++
// instantiating program.


// Define the width of registers and size of memory we use
`define REG_WIDTH   8
`define MEM_SIZE  256


// Top module defines the accessors and instantiates a sub-module with
// substantive content.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   `include "t_dpi_accessors_macros_inc.vh"
   `include "t_dpi_accessors_inc.vh"

   // Put the serious stuff in a sub-module, so we can check hierarchical
   // access works OK.
   test_sub i_test_sub (.clk (clk));

endmodule // t


// A sub-module with all sorts of goodies we would like to access

module test_sub (/*AUTOARG*/
   // Inputs
   clk
   );

   input                    clk;

   integer                  i;		// General counter

   // Elements we would like to access from outside
   reg 	                    a;
   reg [`REG_WIDTH - 1:0]   b;
   reg [`REG_WIDTH - 1:0]   mem [`MEM_SIZE - 1:0];
   wire 		    c;
   wire [`REG_WIDTH - 1:0]  d;
   reg [`REG_WIDTH - 1:0]   e;
   reg [`REG_WIDTH - 1:0]   f;

   // Drive our wires from our registers
   assign  c = ~a;
   assign  d = ~b;

   // Initial values for registers and array
   initial begin
      a = 0;
      b = `REG_WIDTH'h0;

      for (i = 0; i < `MEM_SIZE; i++) begin
	 mem[i] = i [`REG_WIDTH - 1:0];
      end

      e = 0;
      f = 0;
   end

   // Wipe out one memory cell in turn on the positive clock edge, restoring
   // the previous element. We toggle the wipeout value.
   always @(posedge clk) begin
      mem[b]     <= {`REG_WIDTH {a}};
      mem[b - 1] <= b - 1;
      a          <= ~a;
      b          <= b + 1;
   end

endmodule // test_sub
