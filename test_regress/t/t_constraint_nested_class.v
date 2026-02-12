// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

parameter int LEN = 32;

class A;
  rand int x;
  constraint a_c {
    x <= LEN;
    x >= LEN;
  }
endclass

class B;
  rand A a;
endclass

module t;
  B b;
  initial begin
    b = new;
    b.a = new;
    if (b.randomize() == 0) $stop;
    if (b.a.x != LEN) $stop;
    $write("*-* All finished *-*\n");
    $finish;
  end
endmodule
