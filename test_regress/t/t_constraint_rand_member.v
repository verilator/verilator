// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

function automatic int unit_lim();
  return 5;
endfunction

class C;
  static function int lim();
    return 6;
  endfunction
endclass

class A;
  rand int x, y, z, w, u, t, r;
  rand int arr[3];
  int k = 10;
  function int lim();
    return 4;
  endfunction
  function int add(int v);
    return v + 1;
  endfunction
  constraint c {
    x == 100 + lim();
    y == 100 + C::lim();
    z == 100 + unit_lim();
    w == 100 + add(k);
    u == 100 + add(lim());
    t == 100 + this.add(1);
    r == add(x);
    foreach (arr[i]) arr[i] == i + lim();
  }
endclass

class Base;
  virtual function int f();
    return 1;
  endfunction
endclass

class D extends Base;
  rand int s;
  virtual function int f();
    return 2;
  endfunction

  constraint c {s == super.f();}
endclass

class B;
  rand A a;
  rand D d;
  rand int q;
  function new();
    a = new();
    d = new();
  endfunction
  constraint c {q == a.add(a.x);}
endclass

class Outer;
  rand B b;
  function new();
    b = new();
  endfunction
endclass

class E;
  rand int x, y, w;
  function int sum();
    return x + y;
  endfunction
  constraint c {w == sum();}
endclass

class F;
  rand E e;
  rand int v;
  function new();
    e = new();
  endfunction
  constraint c {v == e.sum();}
endclass

module t;
  function automatic void check_a(A a);
    `checkd(a.x, 104);
    `checkd(a.y, 106);
    `checkd(a.z, 105);
    `checkd(a.w, 111);
    `checkd(a.u, 105);
    `checkd(a.t, 102);
    `checkd(a.r, 105);
    foreach (a.arr[i]) `checkd(a.arr[i], i + 4);
  endfunction

  initial begin
    B b;
    Outer o;
    F f;
    int randomize_result;

    b = new();
    randomize_result = b.randomize();
    `checkd(randomize_result, 1);
    check_a(b.a);
    `checkd(b.d.s, 1);
    `checkd(b.q, 105);

    o = new();
    randomize_result = o.randomize();
    `checkd(randomize_result, 1);
    check_a(o.b.a);
    `checkd(o.b.d.s, 1);
    `checkd(o.b.q, 105);

    f = new();
    f.e.x = 1;
    f.e.y = 2;
    randomize_result = f.randomize();
    `checkd(randomize_result, 1);
    `checkd(f.e.w, 3);
    `checkd(f.v, 3);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
