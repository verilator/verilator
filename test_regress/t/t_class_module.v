// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

class Cls;
   class Inner;
      int imemberinnera;
      int imemberinnerb;
   endclass
   int imembera;
   int imemberb;
   Inner innermemberc;
endclass : Cls

class Dead;
endclass

   initial begin
      Cls c;
      if (c != null) $stop;
      c = new;
      if (c.innermemberc != null) $stop;
      c.innermemberc = new;
      c.imembera = 10;
      c.imemberb = 20;
      c.innermemberc.imemberinnera = 30;
      c.innermemberc.imemberinnerb = 40;
      if (c.imembera != 10) $stop;
      if (c.imemberb != 20) $stop;
      if (c.innermemberc.imemberinnera != 30) $stop;
      if (c.innermemberc.imemberinnerb != 40) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
