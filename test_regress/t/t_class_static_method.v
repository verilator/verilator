// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;

  static task static_task(int x);
    $write("Called static task: %d\n", x);
    if (x != 16) $stop;
  endtask

  static function int static_function(int x);
    $write("Called static function: %d\n", x);
    if (x != 23) $stop;
    return 42;
  endfunction

  static function bit static_bit(int x = 5);
    return x == 5;
  endfunction
endclass : Cls

class OCls;
  int i;
  static function OCls create();
    OCls o = new;
    o.i = 42;
    return o;
  endfunction
  static task test_obj(OCls o);
    if (o.i != 42) $stop;
  endtask
endclass

module t;

  initial begin
    int x;
    OCls oc;
    Cls c;

    Cls::static_task(16);
    x = Cls::static_function(23);
    $write("Static function result: %d\n", x);
    if (x != 42) $stop;

    oc = OCls::create();
    OCls::test_obj(oc);

    // Through an object, as a condition, also without parentheses (IEEE 1800-2023 13.5.5)
    c = new;
    if (!c.static_bit()) $stop;
    if (!c.static_bit) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
