// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int imembera;
   function int inc_methoda; imembera += 1; return imembera; endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls c1;
      Cls c2;
      Cls c3;
      c1 = new;
      c1.imembera = 10;
      if (c1.inc_methoda() != 11) $stop;

      // Assignment
      c2 = c1;
      if (c1.inc_methoda() != 12) $stop;
      if (c2.inc_methoda() != 13) $stop;
      if (c1.inc_methoda() != 14) $stop;

      // Shallow copy
      c3 = new c1;

      if (c1.inc_methoda() != 15) $stop;
      if (c3.inc_methoda() != 15) $stop;
      if (c1.inc_methoda() != 16) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
