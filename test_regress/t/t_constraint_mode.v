// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  rand int x;
endclass

class Bar extends Foo;
  rand int y;

  constraint cons_x {x > 0; x < 10;};
  constraint cons_y {y == 10;};
endclass

class Qux extends Bar;
  rand int z;
  rand Bar bar;
  constraint cons_z {z == x || z == y;};

  function new;
    bar = new;
  endfunction

  function void test;
    logic[1:0] ok = 0;
    cons_x.constraint_mode(1);
    if (cons_x.constraint_mode == 0) $stop;
    cons_y.constraint_mode(0);
    if (cons_y.constraint_mode == 1) $stop;
    bar.cons_x.constraint_mode(0);
    if (bar.cons_x.constraint_mode == 1) $stop;
    for (int i = 0; i < 20; ++i) begin
      x = 11;
      y = 12;
      z = 13;
      bar.x = 8;
      bar.y = 9;
      void'(randomize());
      if (x <= 0 || x >= 10) $stop;
      if (y != 10 && y != 12) ok[0] = 1;
      if (z != x && z != y) $stop;
      if (bar.x <= 0 || bar.x >= 10) ok[1] = 1;
      if (bar.y != 10) $stop;
    end
    if (ok != 2'b11) $stop;
    constraint_mode(1);
    if (cons_x.constraint_mode != 1) $stop;
    if (cons_y.constraint_mode != 1) $stop;
    if (cons_z.constraint_mode != 1) $stop;
    x = 14;
    y = 15;
    z = 16;
    void'(randomize());
    if (x <= 0 || x >= 10) $stop;
    if (y != 10) $stop;
    if (z != x && z != y) $stop;
  endfunction
endclass

module t;
  initial begin
    logic[1:0] ok = 0;
    int res;
    Qux qux = new;
    Bar bar = qux;

    qux.test;

    qux.bar.constraint_mode(1);
    bar.cons_y.constraint_mode(1);
    if (bar.cons_y.constraint_mode == 0) $stop;
    qux.cons_z.constraint_mode(0);
    if (qux.cons_z.constraint_mode == 1) $stop;
    qux.bar.cons_y.constraint_mode(0);
    if (qux.bar.cons_y.constraint_mode == 1) $stop;
    for (int i = 0; i < 20; ++i) begin
       qux.x = 17;
       qux.y = 18;
       qux.z = 19;
       qux.bar.x = 20;
       qux.bar.y = 10;
       void'(bar.randomize());
       if (qux.x <= 0 || qux.x >= 10) $stop;
       if (qux.y != 10 && qux.y != 12) $stop;
       if (qux.z != qux.x && qux.z != qux.y) ok[0] = 1;
       if (qux.bar.x <= 0 || qux.bar.x >= 10) $stop;
       if (qux.bar.y != 10) ok[1] = 1;
       res = qux.randomize() with {z == 100;};
       if (qux.z != 100) $stop;
    end
    if (ok != 2'b11) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
