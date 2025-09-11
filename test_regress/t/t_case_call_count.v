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
    bit called = 0;
    foo = new;
    case (foo.get())
      4: $stop;
      5: $stop;
      6: called = 1;
      7: $stop;
      default: $stop;
    endcase
    if (!called) $stop;
    if (foo.callCount != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
