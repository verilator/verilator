// DESCRIPTION: Verilator: Test of select from constant
//
// This tests issue 509, bit select of constant fails
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Jeremy Bennett.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // a and b are arrays of length 1.
   wire  a[0:0];  // Array of nets
   wire  b[0:0];

   assign a = 1'b0;  // Only net assignment allowed
   assign b = a[0];  // Only net assignment allowed

endmodule
