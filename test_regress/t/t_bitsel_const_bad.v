// DESCRIPTION: Verilator: Test of select from constant
//
// This tests issue 508, bit select of constant fails
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Jeremy Bennett.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // Note that if we declare "wire [0:0] b", this works just fine.
   wire  a;
   wire  b;

   assign b = 1'b0;
   assign a = b[0];  // IEEE illegal can't extract scalar

endmodule
