// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

class Cls;
   int imembera;
   int imemberb;
endclass : Cls

class Dead;
endclass

   initial begin
      Cls c;
      if (c != null) $stop;
      c = new;
      c.imembera = 10;
      c.imemberb = 20;
      if (c.imembera != 10) $stop;
      if (c.imemberb != 20) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
