// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Inner;
  rand int x;
endclass

class Outer;
  rand Inner m;
  function Inner get();
    return m;
  endfunction
  constraint c {
    get().x dist {
      5 := 9,
      10 := 1
    };
  }
  function new();
    m = new;
  endfunction
endclass

module t;
  initial begin
    automatic Outer o = new;
    automatic int ok = o.randomize();
    $display("ok=%0d x=%0d", ok, o.m.x);
    $finish;
  end
endmodule
