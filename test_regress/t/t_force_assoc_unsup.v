// DESCRIPTION: Verilator: Verilog Test module
//
// Asserts that forcing through a selection that has no force target of its own,
// such as into an associative array, reports an unsupported error rather than
// forcing nothing.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

module t;

  int a[int];

  initial force a[0] = 1;

endmodule
