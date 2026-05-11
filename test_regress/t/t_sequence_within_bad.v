// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a, b, c, d;

  // Inner length (3) exceeds outer length (1). IEEE 1800-2023 16.9.10
  // requires the inner sequence to fit entirely within the outer match
  // window, so this is a hard error.
  assert property (@(posedge clk)
      (a ##3 b) within (c ##1 d));

endmodule
