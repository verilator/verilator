// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class factory #(
    type T
);
  static function T create;
    T obj = new;
    return obj;
  endfunction
endclass

class foo;
endclass

class bar extends foo;
  static function bar create;
    bar b = new;
    return b;
  endfunction
endclass

module t;
  initial begin
    foo f;
    if (bit'($random)) f = bar::create;
    else f = factory#(foo)::create();
    $finish;
  end
endmodule
;
