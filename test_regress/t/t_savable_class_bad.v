// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int imembera;
endclass : Cls

module t (/*AUTOARG*/);
   initial begin
      Cls c;
      if (c != null) $stop;
      c = new;
      c.imembera = 10;
      if (c.imembera != 10) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
