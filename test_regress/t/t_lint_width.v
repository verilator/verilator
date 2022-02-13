// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t ();

   // This isn't a width violation, as +/- 1'b1 is a common idiom
   // that's fairly harmless
   wire [4:0] five = 5'd5;
   wire [4:0] suma = five + 1'b1;
   wire [4:0] sumb = 1'b1 + five;
   wire [4:0] sumc = five - 1'b1;

   wire [4:0] neg5 = - five;
   wire [5:0] neg6 = - five;

   // Relatively harmless < or <= compared with something less wide
   localparam [1:0] THREE = 3;
   int        a;
   initial for (a = 0; a < THREE; ++a) $display(a);
   initial for (a = 0; a <= THREE; ++a) $display(a);

endmodule
