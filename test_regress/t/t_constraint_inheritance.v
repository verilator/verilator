// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field, cond) \
begin \
   longint prev_result; \
   int ok = 0; \
   for (int i = 0; i < 10; i++) begin \
      longint result; \
      if (!bit'(cl.randomize())) $stop; \
      result = longint'(field); \
      if (!(cond)) $stop; \
      if (i > 0 && result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

typedef class C;

class D extends C;
  constraint x_lt_y { x < y; }
endclass

class A;
endclass

class B extends A;
  rand int x;
  constraint x_gt_0 { x > 0; }
endclass

class C extends B;
  rand int y;
endclass

class E extends C;
  constraint x_lt_20 { x < 20; }
  constraint x_gt_y { x > y; }
endclass

module t;
  initial begin
    B b = new;
    C c = new;
    D d = new;
    E e = new;
    A a = b;
    `check_rand(a, b.x, b.x > 0);
    `check_rand(c, c.x, c.x > 0);
    `check_rand(c, c.y, c.x > 0);
    `check_rand(d, d.x, d.x > 0 && d.x < d.y);
    `check_rand(d, d.y, d.x > 0 && d.x < d.y);
    `check_rand(e, e.x, e.x > 0 && e.x < 20 && e.x > e.y);
    `check_rand(e, e.y, e.x > 0 && e.x < 20 && e.x > e.y);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
