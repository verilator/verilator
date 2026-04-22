// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Foo;
  rand logic foo;
  rand bit bar;
endclass

module t;
  initial begin
    static Foo foo = new;
    if (foo.randomize() == 0) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
