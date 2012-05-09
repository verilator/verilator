// DESCRIPTION: Verilator: Test of selection with unsized Z.
//
// Test selecting Z when size is not explicit. Issue 510.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Jeremy Bennett.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire [1:0]  b;
   wire [1:0]  c;
   wire [0:0]  d;		// Explicit width due to issue 508
   wire [0:0]  e;

   // This works if we use 1'bz, or 1'bx, but not with just 'bz or 'bx. It
   // does require the tri-state Z. Since we get the same effect if b is
   // dimensioned [0:0], this may be connected to issue 508.
   assign b[1:0] = clk ? 2'bx : 'bz;
   assign c[1:0] = clk ? 2'bz : 'bx;
   assign d      = clk ? 1'bx : 'bz;
   assign e      = clk ? 1'bz : 'bx;

endmodule // t
