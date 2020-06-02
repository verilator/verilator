// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module x;

   typedef struct {
      int b [2];
   } notpacked_t;

   notpacked_t n;

   initial begin
      n.b[0] = 1;
      if (n.b[0] != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
