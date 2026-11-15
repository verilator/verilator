// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

module t;
  logic en, d, q;
  always_latch if (en) q <= d;  // <--- Warning

  event ev;
  always_latch if (en) ->>ev;  // Warning

  logic q_waived;
  // verilator lint_off LATCHDLY
  always_latch if (en) q_waived <= d;
  // verilator lint_on LATCHDLY

  logic q_comb_waiver;
  // verilator lint_off COMBDLY
  always_latch if (en) q_comb_waiver <= d;  // Warning
  // verilator lint_on COMBDLY
endmodule
