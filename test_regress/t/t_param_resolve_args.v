// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  static function int get(int x);
    return x;
  endfunction
endclass

class Bar;
  static function int get;
    return 42;
  endfunction
endclass

class Qux #(type Tfoo, type Tbar);
  static function int get();
    return Tfoo::get(Tbar::get());
  endfunction
endclass

module t;
  initial begin
    if (Qux#(Foo, Bar)::get() != 42) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
