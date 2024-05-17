// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int x;
   rand bit [31:0] b;
   rand bit [31:0] c;
   rand bit tiny;

   typedef bit signed [63:0] s64;
   typedef bit [63:0] u64;

   constraint arith { x + x - x == x; }
   constraint divmod { int'((x % 5) / 2) != (b % 99) / 7; }
   constraint mul { x * 9 != b * 3; }
   constraint impl { tiny == 1 -> x != 10; }
   constraint concat { {c, b} != 'h1111; }
   constraint unary { !(-~c == 'h22); }
   constraint log { ((b ^ c) & (b >>> c | b >> c | b << c)) > 0; }
   constraint cmps { x < x || x <= x || x > x || x >= x; }
   constraint cmpu { b < b || b <= b || b > b || b >= b; }
   constraint ext { s64'(x) != u64'(tiny); }

endclass

module t (/*AUTOARG*/);

   Packet p;

   int v;

   initial begin
      p = new;
      v = p.randomize();
      if (v != 1) $stop;
      if ((p.x % 5) / 2 == (p.b % 99) / 7) $stop;
      if (p.x * 9 == p.b * 3) $stop;
      if (p.tiny && p.x == 10) $stop;
      if ({p.c, p.b} == 'h1111) $stop;
      if (-~p.c == 'h22) $stop;
      if (((p.b ^ p.c) & (p.b >>> p.c | p.b >> p.c | p.b << p.c)) <= 0) $stop;
      if (p.x == int'(p.tiny)) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
