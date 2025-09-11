// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  int callCount = 0;
  int value = 6;
  function int get();
    callCount += 1;
    return value;
  endfunction
endclass

module t;
   Foo foo;
   initial begin
      foo = new;
      if (!(foo.get() inside {3,4,5,6,7,8,9})) $stop;
      if (foo.callCount != 1) $stop;
      if (!(foo.get() inside {[3:9]})) $stop;
      if (foo.callCount != 2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
