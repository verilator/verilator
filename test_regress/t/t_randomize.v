// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int header;
   rand int length;
endclass

module t (/*AUTOARG*/);

   Packet p;

   initial begin

      int v;
      v = p.randomize();
      if (v != 1) $stop;
      v = p.randomize(1);
      if (v != 1) $stop;
      v = p.randomize(1, 2);
      if (v != 1) $stop;
      v = p.randomize() with {};
      if (v != 1) $stop;
      // Not testing other randomize forms as unused in UVM

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
