// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class C;
  rand bit [3:0] a;
  rand bit [3:0] b;

  // IEEE 1800-2023 18.5.13: the operand of 'disable soft' must be a
  // constraint_primary (hierarchical identifier with optional select),
  // not a bare expression such as (a + 1).
  constraint c_bad {
    disable soft (a + 1);
  }
endclass

module t;
  initial begin
    $stop;
  end
endmodule
