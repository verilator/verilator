// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class C;
  static function void f(bit x);
    typedef struct {int a;} s_t;
    s_t q[$];
    if (x) return;
    q.push_back('{a: 1});
  endfunction
  // Same typedef name, nested in a block
  static function int g(int x);
    begin
      typedef struct {int b;} s_t;
      s_t q[$];
      if (x == 0) return -1;
      q.push_back('{b: x});
      return q[0].b;
    end
  endfunction
  // Same typedef name, in a task
  static task h(int x, output int o);
    typedef struct {int c;} s_t;
    s_t q[$];
    o = -1;
    if (x == 0) return;
    q.push_back('{c: x});
    o = q[0].c;
  endtask
endclass

module t;
  function automatic int f(int x);
    typedef struct {int a;} s_t;
    s_t q[$];
    if (x == 0) return -1;
    q.push_back('{a: x});
    return q[0].a;
  endfunction
  // Same typedef name, without a return
  function automatic int g(int x);
    typedef struct {int b;} s_t;
    s_t q[$];
    q.push_back('{b: x});
    g = q[0].b + 1;
  endfunction
  task automatic h(int x, output int o);
    typedef struct {int c;} s_t;
    s_t q[$];
    o = -1;
    if (x == 0) return;
    q.push_back('{c: x});
    o = q[0].c;
  endtask
  // Same typedef name, without a return
  task automatic k(int x, output int o);
    typedef struct {int d;} s_t;
    s_t q[$];
    q.push_back('{d: x});
    o = q[0].d + 1;
  endtask

  initial begin
    int o;
    C::f(0);
    `checkd(C::g(0), -1);
    `checkd(C::g(3), 3);
    C::h(0, o);
    `checkd(o, -1);
    C::h(4, o);
    `checkd(o, 4);
    `checkd(f(0), -1);
    `checkd(f(5), 5);
    `checkd(g(7), 8);
    h(0, o);
    `checkd(o, -1);
    h(6, o);
    `checkd(o, 6);
    k(9, o);
    `checkd(o, 10);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
