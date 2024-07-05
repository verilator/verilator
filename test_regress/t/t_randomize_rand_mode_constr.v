// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  rand int a;
  rand int b;
endclass

class Bar;
  rand int x;
  rand Foo foo;

  constraint x_gt_0 {x > 0;};

  function new;
    foo = new;
  endfunction
endclass

class Qux extends Bar;
  rand int y;
  constraint y_gt_x {y > x;};
  constraint y_lt_10 {y < 10;};

  function void test;
    logic ok = 0;
    x.rand_mode(1);
    if (x.rand_mode == 0) $stop;
    y.rand_mode(0);
    if (y.rand_mode == 1) $stop;
    foo.a.rand_mode(0);
    if (foo.a.rand_mode == 1) $stop;
    foo.b.rand_mode(1);
    if (foo.b.rand_mode == 0) $stop;
    for (int i = 0; i < 20; ++i) begin
       x = 4;
       y = 8;
       foo.a = 15;
       foo.b = 16;
       void'(randomize());
       if (x >= y) $stop;
       if (x != 4) ok = 1;
       if (y != 8) $stop;
       if (foo.a != 15) $stop;
       if (foo.b != 16) ok = 1;
     end
     if (!ok) $stop;
     foo.b = 16;
     foo.rand_mode(0);
     if (foo.rand_mode == 1) $stop;
     if (foo.a.rand_mode == 1) $stop;
     if (foo.b.rand_mode == 0) $stop;
     void'(randomize());
     if (foo.a != 15) $stop;
     if (foo.b != 16) $stop;
     ok = 0;
     foo.rand_mode(1);
     if (foo.rand_mode == 0) $stop;
     for (int i = 0; i < 20; ++i) begin
       foo.a = 23;
       foo.b = 42;
       void'(randomize());
       if (foo.a != 23) $stop;
       if (foo.b != 42) ok = 1;
     end
     if (!ok) $stop;
  endfunction
endclass

class Baz;
  Qux qux;

  function new();
    qux = new;
  endfunction

  function void test;
    qux.x = 42;
    qux.rand_mode(0);
    if (qux.x.rand_mode == 1) $stop;
    void'(qux.randomize());
    if (qux.x != 42) $stop;
  endfunction
endclass

class Quux;
  rand int x;
endclass

module t;
  initial begin
    logic ok = 0;
    int res;
    Baz baz = new;
    Qux qux = new;
    Quux quux = new;

    baz.test;
    qux.test;

    qux.x.rand_mode(0);
    if (qux.x.rand_mode == 1) $stop;
    qux.y.rand_mode(1);
    if (qux.y.rand_mode == 0) $stop;
    qux.foo.a.rand_mode(1);
    if (qux.foo.a.rand_mode == 0) $stop;
    qux.foo.b.rand_mode(0);
    if (qux.foo.b.rand_mode == 1) $stop;
    for (int i = 0; i < 20; ++i) begin
       qux.x = 5;
       qux.y = 8;
       qux.foo.a = 13;
       qux.foo.b = 21;
       res = qux.randomize() with {y > 5;};
       if (qux.x >= qux.y) $stop;
       if (qux.y <= 5) $stop;
       if (qux.x != 5) $stop;
       if (qux.y != 8) ok = 1;
       if (qux.foo.a != 13) ok = 1;
       if (qux.foo.b != 21) $stop;
    end
    if (!ok) $stop;

    quux.x.rand_mode(0);
    quux.x = 1000;
    res = quux.randomize() with {x != 1000;};
    if (quux.x != 1000) $stop;
    quux.rand_mode(1);
    res = quux.randomize() with {x != 1000;};
    if (quux.x == 1000) $stop;

    qux.x = 1024;
    qux.y = 512;
    qux.rand_mode(0);
    if (qux.randomize() == 1) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
