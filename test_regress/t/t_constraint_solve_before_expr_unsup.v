// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Cls;
  rand int x;
  rand int y;
  rand int arr[4];

  constraint c { solve arr[0] before y; }  // BAD: non-variable expression
endclass

module t;
  // verilator lint_off IMPLICITSTATIC
  initial begin
    Cls c = new;
    void'(c.randomize());
  end
endmodule
