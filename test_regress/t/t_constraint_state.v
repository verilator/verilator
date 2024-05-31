// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int rf;
   int state;

   constraint c { rf == state; }

endclass

module t (/*AUTOARG*/);

   Packet p;

   int v;

   initial begin
      p = new;
      p.state = 123;
      v = p.randomize();
      if (v != 1) $stop;
      if (p.rf != 123) $stop;

      p.state = 234;
      v = p.randomize();
      if (v != 1) $stop;
      if (p.rf != 234) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
