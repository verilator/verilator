// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class base #(int N = 1);
  rand int x;
endclass
class derived extends base #(2);
  function int apply_inherited(int x);
    return randomize() with {x == 42;};
  endfunction
endclass
class other;
  localparam int OW = 16;
  rand bit [15:0] v;
endclass
class item;
  localparam int W = 32;
  rand int x, y;
  typedef enum {A, B, C} e_t;
  typedef int int_t;
  rand e_t e;
  function int apply_typedef();
    return randomize() with {x == int_t'(5);};
  endfunction
  function int apply_enum();
    return randomize() with {e == B;};
  endfunction
  function int apply_restricted(int x, int y);
    return randomize() with (x) {x == y;};
  endfunction
  function int apply_restricted_param();
    return randomize() with (x, W) {x == W'(45);};
  endfunction
  function int apply_other(other o);
    return o.randomize() with {v == OW'(7);};
  endfunction
  function int apply_value(int x);
    return this.randomize() with {x == local::x;};
  endfunction
  function int apply_both(int want_x, int want_y);
    return randomize(x, y) with {x == local::want_x; y == local::want_y;};
  endfunction
  function int apply_param();
    return randomize() with {x == W'(44);};
  endfunction
  function int apply_std(output int a);
    return std::randomize(a) with {a == y;};
  endfunction
endclass
module t;
  initial begin

    automatic item it = new;
    automatic derived d = new;
    automatic other o = new;
    int a;
    int ok;
    it.x = -1;
    ok = it.apply_value(42);
    `checkd(ok, 1);
    `checkd(it.x, 42);
    ok = it.apply_both(11, 24);
    `checkd(ok, 1);
    `checkd(it.x, 11);
    `checkd(it.y, 24);
    ok = it.apply_param();
    `checkd(ok, 1);
    `checkd(it.x, 44);
    ok = it.apply_std(a);
    `checkd(ok, 1);
    `checkd(a, it.y);
    ok = d.apply_inherited(7);
    `checkd(ok, 1);
    `checkd(d.x, 42);
    ok = std::randomize(a) with {a == 3;};
    `checkd(ok, 1);
    `checkd(a, 3);
    ok = it.apply_typedef();
    `checkd(ok, 1);
    `checkd(it.x, 5);
    ok = it.apply_enum();
    `checkd(ok, 1);
    `checkd(it.e, item::B);
    ok = it.apply_restricted(1, 9);
    `checkd(ok, 1);
    `checkd(it.x, 9);
    ok = it.apply_restricted_param();
    `checkd(ok, 1);
    `checkd(it.x, 45);
    ok = it.apply_other(o);
    `checkd(ok, 1);
    `checkd(o.v, 7);
    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
