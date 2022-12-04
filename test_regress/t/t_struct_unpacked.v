// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module x;
   typedef struct {
      int a, b;
      logic [3:0] c;
   } embedded_t;

   typedef struct {
      embedded_t b;
      embedded_t tab [3:0];
   } notembedded_t;

   notembedded_t p;
   embedded_t t [1:0];

   initial begin
      t[1].a = 2;
      p.b.a = 1;
      if (t[1].a != 2) $stop;
      if (p.b.a != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
