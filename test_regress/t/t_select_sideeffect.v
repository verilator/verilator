// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  int x = 0;
  function int get();
    x += 1;
    return x;
  endfunction
endclass

module t;
  Foo foo;
  int x[3] = {0, 2, 0};
  initial begin
    foo = new;
    if (x[foo.get()] != 2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
