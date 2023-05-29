// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   typedef struct {
      int fst, snd;
   } pair_t;

   class Cls;
      pair_t p;
   endclass

   pair_t a, b;
   Cls c = new;

   initial begin
      a.fst = 1;
      a.snd = 2;
      b.fst = 3;
      b.snd = 4;

      a = b;

      $display("(%d, %d) (%d, %d)", a.fst, a.snd, b.fst, b.snd);
      $display("%%p=%p", a);

      c.p.fst = 5;
      if (c.p.fst != 5) $stop;
      a = c.p;
      if (a.fst != 5) $stop;
      c.p = b;
      if (c.p.fst != 3) $stop;
      if (c.p.snd != 4) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
