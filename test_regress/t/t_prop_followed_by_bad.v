// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);

  input clk;

  reg a = 0;
  reg b = 0;
  reg c = 0;

  // True multi-cycle sequence LHS of followed-by is not yet supported.
  // IEEE 1800-2023 16.12.9 allows sequence_expr #-# property_expr, but the
  // NFA needs a different fail detector for sequence-failure than for
  // boolean-failure (see V3AssertNfa::buildImplication). Rejected with an
  // explicit UNSUPPORTED message.
  assert property (@(posedge clk) (a ##1 b) #-# c);

  // Followed-by embedded inside boolean property connectives (`implies`, `iff`)
  // is currently unsupported: NFA claims the assertion but only routes
  // top-level / directly-reachable AstImplication through the followed-by
  // NFA builder. A loud UNSUPPORTED beats a silent lowering-as-plain-implication.
  assert property (@(posedge clk) (a #-# b) iff c);

endmodule
