// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int one;
   rand int two;

   extern function void f();
   constraint cone;
   extern constraint ctwo;
   constraint cmissing;  // Ok per IEEE 1800-2023 18.5.1

endclass

constraint Packet::cone { one > 0 && one < 2; }

constraint Packet::ctwo { two > 1 && two < 3; }

function void Packet::f();
endfunction

module t (/*AUTOARG*/);

   Packet p;

   int v;

   initial begin
      p = new;
      v = p.randomize();
      if (v != 1) $stop;
      if (p.one != 1) $stop;
      if (p.two != 2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
