// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

class RandomValue;
  rand int value;
  constraint small_int_c {
    value < 10;
  }
  task disable_val();
    value.rand_mode(0);
  endtask
endclass

class Base;
endclass

class Foo extends Base;
  rand RandomValue v = new;
endclass

module t;
  Base b;
  initial begin
    automatic Foo d = new;
    b = d;
    d.v.disable_val();
    d.v.value = 11;
    if (bit'(b.randomize())) $stop;
    if (d.v.value != 11) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
