// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Zero-repetition and folded-operand composites reach the NFA under --bbox-unsup

module t (
    input clk
);

  logic a, b, c, d, x;

  // verilog_format: off
  assert property (@(posedge clk) (a[*0]) and (b ##1 c));

  assert property (@(posedge clk) (a[*0]) and (b ##[1:2] c));

  assert property (@(posedge clk) ((a[*0]) ##1 b ##1 c) intersect (d ##2 c));

  assert property (@(posedge clk) (a ##1 b) or (accept_on(x) (c ##1 d)));

  assert property (@(posedge clk) (accept_on(x) (a ##1 b)) and (c ##2 d));
  // verilog_format: on

  always @(posedge clk) begin
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
