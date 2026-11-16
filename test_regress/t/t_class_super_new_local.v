// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Base;
  int v;
  function new(int a);
    v = a;
  endfunction
endclass

class D extends Base;
  int m = v + 1;
  function new(int a);
    int t = a * 2;
    super.new(t);
  endfunction
endclass

module t;
  initial begin
    D d;
    d = new(3);
    if (d.v != 6) $stop;
    if (d.m != 7) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
