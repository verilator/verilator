// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aditya Shevade
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 18.4: a member of an unpacked struct is random only if
// its own declaration carries rand/randc; the containing struct being
// rand does not imply that. Here no member does, so randomize() on obj
// must leave the whole struct untouched.
typedef struct {
  int a;
  bit [7:0] b;
} AllUnmarked;

class C;
  rand AllUnmarked s;
  function new();
    s.a = 42;
    s.b = 8'ha5;
  endfunction
endclass

module t;
  initial begin
    C obj;
    obj = new;
    repeat (10) begin
      if (obj.randomize() == 0) $stop;
      if (obj.s.a != 42) $stop;
      if (obj.s.b != 8'ha5) $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
