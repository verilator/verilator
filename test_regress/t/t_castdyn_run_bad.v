// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Base;
endclass
class C;
endclass

module t (/*AUTOARG*/);
   int i;

   Base b;
   C c;

   initial begin
      b = new;
      i = $cast(c, b);
      if (i != 0) $stop;

      $cast(c, b);  // Bad at runtime

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
