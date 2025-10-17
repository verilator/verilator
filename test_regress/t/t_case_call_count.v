// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Cls;
  int callCount = 0;
  int callCount2 = 0;
  int value = 6;
  bit[5:0] value2 = 6;
  function int get();
    callCount += 1;
    return value;
  endfunction
  function bit[5:0] get2();
    callCount2 += 1;
    return value2;
  endfunction
  function int getPure();
    return callCount2;
  endfunction
endclass

module t;
  Cls c;
  initial begin
    bit called = 0;
    c = new;
    case (c.get())
      4: $stop;
      5: $stop;
      6: called = 1;
      7: $stop;
      default: $stop;
    endcase
    if (!called) $stop;
    if (c.callCount != 1) $stop;
    called = 0;
    case (c.get2())
      4: $stop;
      5: $stop;
      6: called = 1;
      7: $stop;
      default: $stop;
    endcase
    case (c.getPure())
      1:;
      default: $stop;
    endcase
    if (!called) $stop;
    if (c.callCount2 != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
