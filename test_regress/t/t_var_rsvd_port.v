// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   bool
   );

   input bool;  // BAD

   reg  vector; // OK, as not public
   reg  switch /*verilator public*/;    // Bad

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
