// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   typedef struct {
      int fst, snd;
   } pair_t;

   pair_t a, b;

   initial begin
      a.fst = 1;
      a.snd = 2;
      b.fst = 3;
      b.snd = 4;

      a = b;

      $display("(%d, %d) (%d, %d)", a.fst, a.snd, b.fst, b.snd);
      $display("%%p=%p", a);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
