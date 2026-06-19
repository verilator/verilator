// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Foo;
  rand int abcd;
endclass

class Bar;
  rand Foo foo_arr[];

  function new();
    foo_arr = new[12];
    foreach (foo_arr[i]) foo_arr[i] = new;
  endfunction

  constraint c {
    foo_arr.size() == 10;
    foreach (foo_arr[i]) foo_arr[i].abcd < 8;
  }
endclass

module t;
  Bar bar;
  initial begin
    bar = new();
    bar.randomize();
    if (bar.foo_arr.size() != 10) $stop;
    foreach (bar.foo_arr[i]) begin
      if (bar.foo_arr[i] >= 8) $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
