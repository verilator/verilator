// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Property if/else control forms the fail-only count engine cannot lower.

module t (
    input clk
);

  bit a;
  bit b;
  bit c;

  assert property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c) $display("pass");
  cover property (@(posedge clk) if (a) 1'b1 ##1 b else 1'b1 ##2 c);
  assert property (@(posedge clk) not (if (a) 1'b1 ##1 b else 1'b1 ##2 c));

  assert property (@(posedge clk) if (a) s_always[1:2] b else 1'b1 ##1 c);

  assert property (@(posedge clk)
                   if ($random == 0) 1'b1 ##1 b
                   else 1'b1 ##1 c);

endmodule
