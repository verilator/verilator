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
class item;
  localparam int W = 32;
  rand int x, y;
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
    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
