// DESCRIPTION: Verilator: Verilog Test module
//
// Simple test for unpacked concatenation arrays used as function arguments.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-License-Identifier: CC0-1.0
//

class A;
  int r1[2];
  int r2;
endclass

class B;
  virtual function int B_virt_func(int r[3], p[4]);
    return r[0] + r[1] + r[2] + p[0] + p[1] + p[2] + p[3];
  endfunction
endclass

function int func_1_concat(int r[4]);
  // verilator no_inline_task
  return r[0] + r[1] + r[2] + r[3];
endfunction

function int func_2_concat(int r[3], int p[4]);
  // verilator no_inline_task
  return r[0] + r[1] + r[2] + p[0] + p[1] + p[2] + p[3];
endfunction

module t;
  int s;
  A a = new;
  B b = new;
  initial begin
    a.r1 = {1, 2};
    a.r2 = 5;
    s = func_1_concat({a.r1, a.r1});
    if (s != 6) $stop;

    s = func_2_concat({a.r1, a.r2}, {a.r1, a.r1});
    if (s != 14) $stop;

    s = b.B_virt_func({a.r1, a.r2}, {a.r1, a.r1});
    if (s != 14) $stop;

    $write("*-* All finished *-*\n");
    $finish;
  end
endmodule
