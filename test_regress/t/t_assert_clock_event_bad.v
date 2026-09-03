// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// 'this' and 'super' are not legal clocking event operands (IEEE 1800-2023 A.6.5)
module t (
  input clk
);
  logic a;

  assert property (@this.clk a |-> a);
  assert property (@super.clk a |-> a);
endmodule
