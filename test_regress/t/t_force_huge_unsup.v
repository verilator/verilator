// DESCRIPTION: Verilator: Verilog Test module
//
// A variable with more force slots (leaves) than the int slot arithmetic can
// hold is rejected rather than numbering its slots wrongly and miscompiling.
// The array is only its type here, so this stays cheap to elaborate.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

module t;
  // 46341 * 46341 = 2147488281 > 2^31 - 1 leaves
  bit x[46341][46341];
  initial begin
    force x[0][0] = 1'b1;
    release x[0][0];
    $finish;
  end
endmodule
