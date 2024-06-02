// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Base;
   pure constraint pur;
endclass

class Packet extends Base;
   rand int header;
   rand int length;

   constraint pur { length == 3; }

   extern constraint ex;

endclass

constraint Packet::ex { header == 2; }

module t (/*AUTOARG*/);

   Packet p;

   initial begin

      int v;
      v = p.randomize();
      if (v != 1) $stop;
      if (p.header != 2) $stop;
      if (p.length != 3) $stop;
      v = p.randomize(1);
      if (v != 1) $stop;
      if (p.header != 2) $stop;
      if (p.length != 3) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
