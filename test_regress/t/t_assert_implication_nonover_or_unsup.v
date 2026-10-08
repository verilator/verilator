// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Marco Brambilla
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  logic x, y, b, c;

  // A disjunction as the antecedent of followed-by stays unsupported
  assert property (@(posedge clk) ((x or y) #-# b) or c);
  assert property (@(posedge clk) (x or y) #=# b);
  assert property (@(posedge clk) (x or y) #-# s_eventually b);

endmodule
