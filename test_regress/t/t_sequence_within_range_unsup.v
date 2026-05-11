// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (input clk);
  logic a, b, c, d;

  // Ranged cycle-delay in the inner arm is not lowerable: each length
  // in the range would admit a different offset set. IEEE 1800-2023
  // 16.9.10 is not well-defined under variable-length operands for our
  // fixed-length desugar, so reject with UNSUPPORTED.
  assert property (@(posedge clk)
      (a ##[1:3] b) within (c ##5 d));

endmodule
