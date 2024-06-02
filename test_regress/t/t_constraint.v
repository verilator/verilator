// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int one;

   constraint a { one > 0 && one < 2; }

endclass

module t (/*AUTOARG*/);

   Packet p;

   int v;

   initial begin
      p = new;
      v = p.randomize();
      if (v != 1) $stop;
      if (p.one != 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
