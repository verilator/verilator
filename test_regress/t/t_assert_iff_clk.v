// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  int cyc;
  logic rst = 1'b1;
  logic x = 1'b1;
  int issue_fail;
  int pre_fail;
  int post_fail;
  int pre_temporal_fail;
  int post_temporal_fail;

  a_issue: assert property (disable iff(rst !== 1'b0) @(posedge clk) !x)
    else issue_fail++;

  assert property (disable iff (cyc < 5) @(posedge clk) 0)
    else pre_fail++;

  assert property (@(posedge clk) disable iff (cyc < 5) 0)
    else post_fail++;

  assert property (disable iff (cyc < 5) @(posedge clk) 1 ##1 0)
    else pre_temporal_fail++;

  assert property (@(posedge clk) disable iff (cyc < 5) 1 ##1 0)
    else post_temporal_fail++;

  always @(negedge clk) begin
    cyc <= cyc + 1;
    rst <= cyc < 4;
    x <= cyc < 4;
    if (cyc == 12) begin
      if (issue_fail != 0) $stop;
      if (pre_fail != post_fail) $stop;
      if (pre_temporal_fail != post_temporal_fail) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
