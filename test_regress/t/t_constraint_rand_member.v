// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

function automatic int unit_lim();
  return 5;
endfunction

class C;
  static function int lim();
    return 6;
  endfunction
endclass

class A;
  rand int x, y, z, w;
  int k = 10;
  function int lim();
    return 4;
  endfunction
  function int add(int v);
    return v + 1;
  endfunction
  constraint c {
    x == 100 + lim();
    y == 100 + C::lim();
    z == 100 + unit_lim();
    w == 100 + add(k);
  }
endclass

class B;
  rand A a;
  function new();
    a = new();
  endfunction
endclass

module t;
  initial begin
    B b;
    b = new();
    void'(b.randomize());

    if (b.a.x != 104) begin
      $write("%%Error: x=%0d, expected 104\n", b.a.x);
      $stop;
    end
    if (b.a.y != 106) begin
      $write("%%Error: y=%0d , expected 106\n", b.a.y);
      $stop;
    end
    if (b.a.z != 105) begin
      $write("%%Error: z=%0d, expected 105\n", b.a.z);
      $stop;
    end
    if (b.a.w != 111) begin
      $write("%%Error: w=%0d, expected 111\n", b.a.w);
      $stop;
    end
    $finish;
  end
endmodule
