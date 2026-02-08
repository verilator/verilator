// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

class A;
  rand int j;
endclass

class B;
  A a;
  rand int i;
  function new();
    a = new;
    i = 7;
  endfunction
  task r();
    if (a.randomize() with {j == i;} == 0) $stop;
  endtask
endclass

module t;
  initial begin
    automatic B b = new;
    b.r();
    if (b.a.j != 7) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
