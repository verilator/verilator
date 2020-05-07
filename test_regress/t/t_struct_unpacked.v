// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module x;

   // verilator lint_off UNPACKED
   typedef struct {
      int         a;
   } notpacked_t;
   // verilator lint_on UNPACKED

   typedef struct packed {
      notpacked_t b;
   } ispacked_t;

   ispacked_t p;

   initial begin
      p.b = 1;
      if (p.b != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
