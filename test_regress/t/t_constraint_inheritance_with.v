// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field, constr, cond) \
begin \
   longint prev_result; \
   int ok = 0; \
   if (!bit'(cl.randomize() with { constr; })) $stop; \
   prev_result = longint'(field); \
   if (!(cond)) $stop; \
   repeat(9) begin \
      longint result; \
      if (!bit'(cl.randomize() with { constr; })) $stop; \
      result = longint'(field); \
      if (!(cond)) $stop; \
      if (result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

typedef class C;

class D extends C;
  rand int z;
  constraint x_lt_y { x < y; }
endclass

class A;
  rand int x;
endclass

class B extends A;
  constraint x_gt_0 { x > 0; }
endclass

class C extends B;
  rand int y;
endclass

class E extends C;
  constraint x_gt_y { x > y; }
endclass

module t;
  initial begin
    B b = new;
    C c = new;
    D d = new;
    E e = new;
    A a = b;
    `check_rand(a, a.x, x < 10, a.x > 0 && a.x < 10);
    `check_rand(c, c.x, x < 100, c.x > 0 && c.x < 100);
    `check_rand(c, c.y, x == 5, c.x == 5);
    `check_rand(d, d.x, z > x && z < y, d.x > 0 && d.x < d.y);
    `check_rand(d, d.y, z > x && z < y, d.x > 0 && d.x < d.y);
    `check_rand(e, e.x, x inside {[10:20]}, e.x inside {[10:20]} && e.x > e.y);
    `check_rand(e, e.y, x inside {[10:20]}, e.x inside {[10:20]} && e.x > e.y);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
