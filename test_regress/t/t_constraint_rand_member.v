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
  rand int x, y, z, w;
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
  }
endclass

class B;
  rand A a;
  function new();
    a = new();
  endfunction
endclass

module t;
  initial begin
    B b;
    int ok;
    b = new();
    ok = b.randomize();
    `checkd(ok, 1);
    `checkd(b.a.x, 104);
    `checkd(b.a.y, 106);
    `checkd(b.a.z, 105);
    `checkd(b.a.w, 111);
    $finish;
  end
endmodule
