// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   o,
   // Inputs
   i
   );

   // Need some logic to get mtask debug fully covered
   input i;
   output wire o;
   assign o = i;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
