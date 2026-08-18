// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Assoc;
  rand int unsigned m[int];
  rand int unsigned s;
  constraint c {
    solve m before s;
    m.size() == 2;
  }
endclass

module t;
  Assoc o;
  initial begin
    o = new;
    void'(o.randomize());
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
