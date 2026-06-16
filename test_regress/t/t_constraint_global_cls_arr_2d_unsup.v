// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Foo;
  rand int abcd;
   constraint c { abcd >= 2; }
endclass

class Bar;
  rand Foo foo_arr[$][];

  function new();
    for (int i = 0; i < 3; i++) foo_arr[i] = new[5];
    foreach(foo_arr[i, j]) foo_arr[i][j] = new;
  endfunction

  constraint c {
    foo_arr.size() == 10;
    foreach (foo_arr[i, j]) foo_arr[i][j].abcd < 8;
  }
endclass

module t;
  Bar bar;
  initial begin
    bar = new();
    void'(bar.randomize());
    if (bar.foo_arr.size() != 10) $stop;
    foreach (bar.foo_arr[i, j]) begin
      if (bar.foo_arr[i][j].abcd < 2 || bar.foo_arr[i][j].abcd >= 8) $stop;
    end
    for (int i = 3; i < 10; i++) begin
      if (bar.foo_arr[i].size() != 0) $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
