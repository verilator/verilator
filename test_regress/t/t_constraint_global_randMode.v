// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by PlanV GmbH.
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
  rand RandomValue v = new;
endclass

class Foo extends Base;
endclass

module t;
  initial begin
    Foo d = new;
    Base b = d;
    b.v.disable_val();
    b.v.value = 11;
    if (bit'(b.randomize())) $stop;
    if (b.v.value != 11) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
