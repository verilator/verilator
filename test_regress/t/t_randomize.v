// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int header;
   rand int length;

   extern constraint ex;

   constraint a { header > 0 && header < 1000; }
   constraint b {
      if (64 > header) {
         header < (64'h1 << length);
      }
   }
   constraint b {
      header >= length - 10;
      header <= length;
   }
   constraint c {
      foreach (in_use[i]) {
         !(start_offset <= in_use[i].Xend_offsetX &&
           start_offset + len - 1 >= in_use[i].Xstart_offsetX);
      }
   }
   constraint order { solve length before header; }
   constraint dis {
      disable soft x;
      x dist { [100:102] :/ 1, 200 := 2, 300 := 5, 400};
   }

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
