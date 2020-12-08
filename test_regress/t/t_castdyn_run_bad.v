// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Base;
endclass
class ExbaseA extends Base;
endclass
class ExbaseB extends Base;
endclass

module t (/*AUTOARG*/);
   int i;

   Base b;
   ExbaseA ba, ba1;
   ExbaseB bb, bb1;

   initial begin
      ba = new;
      b = ba;
      i = $cast(ba1, b);
      if (i != 1) $stop;
      $cast(ba1, b);  // ok at runtime

      bb = new;
      b = bb;
      i = $cast(ba1, b);
      if (i != 0) $stop;
      $cast(ba1, b);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
