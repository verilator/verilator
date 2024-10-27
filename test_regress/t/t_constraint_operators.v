// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int x;
   rand bit [31:0] b;
   rand bit [31:0] c;
   rand bit [31:0] d;
   rand bit tiny;
   rand bit zero;
   rand bit one;
   rand int out0, out1, out2, out3, out4, out5, out6;

   bit state;

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
   constraint cond { (tiny == 1 ? b : c) != 17; }
   constraint zero_c { zero == 0; }
   constraint one_c { one == 1; }
   constraint sel { d[15:8] == 8'h55; }
   constraint ifelse {
      if (one) out0 == 'h333;

      if (!one) tiny != tiny;
      else out1 == 'h333;
      if (one == 1) out2 == 'h333;
      else tiny != tiny;
      if (0) tiny != tiny;
      else out3 == 'h333;
      if (1) out4 == 'h333;
      else tiny != tiny;

      if (one == 1)
         if (1) { out5 == 'h333; out5 == 'h333; out5 == 'h333; }
         else tiny != tiny;
      else
         if (1) tiny != tiny;
         else { tiny != tiny; }

      if (1)
         if (one == 1) { out6 == 'h333; out6 == 'h333; out6 == 'h333; }
         else tiny != tiny;
      else
         if (one == 1) tiny != tiny;
         else { tiny != tiny; }

      if (one && zero) tiny != tiny;
      if (~one && zero) tiny != tiny;
      if (zero || (one & zero)) tiny != tiny;
      if (zero && (one | zero)) tiny != tiny;
   }

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
      if ((p.tiny == 1 ? p.b : p.c) == 17) $stop;
      if ((p.tiny == 1 ? p.b : p.c) == 17) $stop;
      if (p.zero != 0) $stop;
      if (p.one != 1) $stop;
      if (p.out0 != 'h333) $stop;
      if (p.out1 != 'h333) $stop;
      if (p.out2 != 'h333) $stop;
      if (p.out3 != 'h333) $stop;
      if (p.out4 != 'h333) $stop;
      if (p.out5 != 'h333) $stop;
      if (p.out6 != 'h333) $stop;
      if (p.d[15:8] != 'h55) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
