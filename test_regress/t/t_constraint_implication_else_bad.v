// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class C;
  rand bit [3:0] a;
  rand bit [3:0] b;

  // IEEE 1800-2023 18.7.2: implication operator -> takes one constraint_set
  // on the RHS; it is single-armed (no else clause). Only the if (...) form
  // accepts an optional else branch.
  constraint c_bad {
    (a == 0) -> { b == 4'h1; } else { b == 4'h2; }
  }
endclass

module t;
  initial begin
    $stop;
  end
endmodule
