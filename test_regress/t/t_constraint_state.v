// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0


`define check_rand(cl, field, cond) \
begin \
   longint prev_result; \
   int ok = 0; \
   if (!bit'(cl.randomize())) $stop; \
   prev_result = longint'(field); \
   if (!(cond)) $stop; \
   repeat(9) begin \
      longint result; \
      if (!bit'(cl.randomize())) $stop; \
      result = longint'(field); \
      if (!(cond)) $stop; \
      if (result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

class Foo;
   int x;
endclass

class Bar;
   rand int y;
endclass

class Packet;
   rand int rf;
   int state;
   rand int a;
   rand Foo foo;
   Bar bar;

   constraint c1 { rf == state; }
   constraint c2 { a > foo.x; a < bar.y; }

   function new(int s, int x, int y);
      state = s;
      foo = new;
      foo.x = x;
      bar = new;
      bar.y = y;
   endfunction
endclass

module t (/*AUTOARG*/);

   Packet p;

   int v;

   initial begin
      p = new(123, 10, 20);
      v = p.randomize();
      if (v != 1) $stop;
      if (p.rf != 123) $stop;

      `check_rand(p, p.a, p.a > 10 && p.a < 20)
      if (p.foo.x != 10) $stop;
      if (p.bar.y != 20) $stop;

      p.state = 234;
      v = p.randomize();
      if (v != 1) $stop;
      if (p.rf != 234) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
