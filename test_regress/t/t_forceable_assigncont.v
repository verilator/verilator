// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Zubin Jain
// SPDX-License-Identifier: CC0-1.0

module t;
  logic forceable_q  /*verilator forceable*/ = 1'b0;
  logic assigned_q = 1'b0;

  // Regression for V3Force: assignAll() should reuse the helper vars created by
  // forceAll() for a forceable signal instead of generating a duplicate set.
  initial assign assigned_q = forceable_q;
endmodule
