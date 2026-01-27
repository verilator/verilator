// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Base;
  int j;
  function new(int x);
    j = x;
  endfunction
  static function int get_default();
    return 8;
  endfunction
endclass
class Derived extends Base;
  function new();
    super.new(get_default());
  endfunction
endclass

module t;
  initial begin
    Derived d = new;
    if (d.j != 8) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
