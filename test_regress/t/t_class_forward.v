// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package P;
   typedef class ClsB;
class ClsA;
   int imembera;
   ClsB b;
endclass
class ClsB;
   int imemberb;
   ClsA a;
endclass
endpackage

module t (/*AUTOARG*/);
   P::ClsA ca;
   P::ClsB cb;
   initial begin
      // Alternate between two versions to make sure we don't
      // constant propagate between them.
      ca = new;
      cb = new;
      ca.b = new;
      cb.a = new;
      ca.imembera = 100;
      ca.b.imemberb = 111;
      cb.imemberb = 200;
      cb.a.imembera = 202;
      if (ca.imembera != 100) $stop;
      if (ca.b.imemberb != 111) $stop;
      if (cb.imemberb != 200) $stop;
      if (cb.a.imembera != 202) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
