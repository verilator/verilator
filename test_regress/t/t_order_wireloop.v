// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   bar
   );

   wire  foo;
   output  bar;

   // Oh dear.
   assign  foo = bar;
   assign  bar = foo;

endmodule
