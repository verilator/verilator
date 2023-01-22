// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module x;

   typedef union {
      int         a;
   } union_t;

   union_t b;

   initial begin
      b = 1;
      if (b != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
