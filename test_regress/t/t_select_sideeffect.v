// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  bit [2:0] x = 0;
  function int get();
    x += 1;
    return int'(x);
  endfunction
  function bit [2:0] get2();
    x += 1;
    return x;
  endfunction
endclass

module t;
  Foo foo;
  int x[5] = {1, 2, 3, 4, 5};
  initial begin
    foo = new;
    if (x[foo.get()] != 2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
  always begin
    if (x[foo.get2()] != 3) $stop;
  end
  final begin
    if (x[foo.get()] != 4) $stop;
  end
endmodule
