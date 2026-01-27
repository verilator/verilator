// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

typedef class Derived;
class Base;
  function Derived cast();
    if (!$cast(cast, this)) begin end
  endfunction
endclass

class Derived extends Base;
  string x;
  function new(string xval);
    x = xval;
  endfunction
  function string get();
    return x;
  endfunction
endclass

module t;
  initial begin
    Derived d = new("Hello");
    Base b = d;
    Derived c = b.cast();
    if (d.get() != c.get()) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
