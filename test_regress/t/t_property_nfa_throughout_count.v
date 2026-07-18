// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// A throughout guard drop fails each live delay-ring attempt independently.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  bit fixed_start = 0;
  bit fixed_guard = 1;
  bit drop_tag = 0;
  int fixed_fail = 0;
  int negated_pass = 0;
  int negated_cover = 0;

  bit range_start = 0;
  bit range_guard = 1;
  bit range_done = 0;
  int range_fail = 0;

  bit disable_now = 0;
  bit disabled_guard = 1;
  int disabled_fail = 0;

  bit kill_start = 0;
  bit kill_guard = 1;
  int kill_fail = 0;

  assert property (@(posedge clk) fixed_start |-> (fixed_guard throughout (1'b1 ##300 1'b1)))
  else fixed_fail++;

  assert property (@(posedge clk) not (fixed_guard throughout (fixed_start ##300 1'b1))) begin
    if (drop_tag) negated_pass++;
  end
  cover property (@(posedge clk) not (fixed_guard throughout (fixed_start ##300 1'b1))) begin
    if (drop_tag) negated_cover++;
  end

  assert property (@(posedge clk)
      range_start |-> (range_guard throughout (1'b1 ##[1:300] range_done)))
  else range_fail++;

  assert property (@(posedge clk) disable iff (disable_now)
      fixed_start |-> (disabled_guard throughout (1'b1 ##300 1'b1)))
  else disabled_fail++;

  assert property (@(posedge clk) kill_start |-> (kill_guard throughout (1'b1 ##300 1'b1)))
  else kill_fail++;

  initial begin
    @(negedge clk) begin
      fixed_start = 1;
      range_start = 1;
    end
    repeat (2) @(negedge clk);
    @(negedge clk) begin
      fixed_start = 0;
      fixed_guard = 0;
      drop_tag = 1;
      range_start = 0;
      range_guard = 0;
      disable_now = 1;
      disabled_guard = 0;
    end
    #1 disable_now = 0;
    @(negedge clk) begin
      `checkd(fixed_fail, 3);
      `checkd(range_fail, 3);
      `checkd(negated_pass, 4);
      `checkd(negated_cover, 4);
      `checkd(disabled_fail, 0);
      drop_tag = 0;
      kill_start = 1;
    end

    repeat (2) @(negedge clk);
    @(negedge clk) begin
      kill_start = 0;
      kill_guard = 0;
      $assertkill;
      $asserton;
    end
    @(negedge clk) begin
      `checkd(kill_fail, 0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
