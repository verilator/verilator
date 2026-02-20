// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Base;
  int k = 3;
  function new(int x);
    k = x;
  endfunction
  protected function int get_x_base();
    Base f = this;
    return 7;
  endfunction
endclass

class Foo extends Base;
  function new(int x);
    super.new(x);
  endfunction

  protected function int get_x();
    Foo f = this;
    return get_x_base();
  endfunction
endclass

class Bar extends Foo;
  function new();
    super.new(get_x());
  endfunction
endclass

module top;
  initial begin
    static Bar b = new();
    if (b.k != 7) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
