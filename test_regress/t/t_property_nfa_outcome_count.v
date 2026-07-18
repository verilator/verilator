// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Multiple attempts maturing in one time slot are counted per attempt.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  bit implication_a = 1;
  bit implication_b = 0;
  bit chain_a = 1;
  bit chain_b = 0;
  bit chain_c = 0;
  bit range_a = 1;
  bit range_b = 0;
  int implication_pass = 0;
  int implication_fail = 0;
  int chain_pass = 0;
  int chain_fail = 0;
  int range_pass = 0;
  int range_fail = 0;
  int range_cover = 0;
  bit small_checked = 0;

  initial $assertpasson;

  assert property (@(posedge clk) implication_a |-> ##1 implication_b) implication_pass++;
  else implication_fail++;

  assert property (@(posedge clk) chain_a ##1 chain_b ##1 chain_c) chain_pass++;
  else chain_fail++;

  assert property (@(posedge clk) range_a ##[1:2] range_b) range_pass++;
  else range_fail++;
  cover property (@(posedge clk) range_a ##[1:2] range_b) range_cover++;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      implication_a <= 0;
      chain_a <= 1;
      chain_b <= 1;
      range_a <= 1;
      range_b <= 0;
    end
    else if (cyc == 1) begin
      implication_a <= 0;
      implication_b <= 0;
      chain_a <= 0;
      chain_b <= 0;
      chain_c <= 1;
      range_a <= 0;
      range_b <= 1;
    end
  end

  initial begin
    repeat (3) @(negedge clk);
    `checkd(implication_pass, 2);
    `checkd(implication_fail, 1);
    `checkd(chain_pass, 1);
    `checkd(chain_fail, 2);
    `checkd(range_pass, 2);
    `checkd(range_fail, 1);
    `checkd(range_cover, 2);
    small_checked = 1;
  end

  bit large_a = 0;
  bit large_b = 0;
  bit large_abort = 0;
  bit large_disable = 0;
  int large_pass = 0;
  int large_fail = 0;
  int large_cover = 0;
  int large_implication_at_b = 0;
  int large_accept_pass = 0;
  int large_accept_fail = 0;
  int large_reject_pass = 0;
  int large_reject_fail = 0;
  int large_disable_accept_pass = 0;
  int large_disable_accept_fail = 0;

  assert property (@(posedge clk) large_a ##[1:300] large_b) large_pass++;
  else large_fail++;
  cover property (@(posedge clk) large_a ##[1:300] large_b) large_cover++;
  assert property (@(posedge clk) large_a |-> ##[1:300] large_b)
    if (large_b) large_implication_at_b++;
  assert property (@(posedge clk) sync_accept_on (large_abort) (large_a |-> ##[1:300] large_b)) begin
    if (large_abort) large_accept_pass++;
  end
  else if (large_abort) large_accept_fail++;
  assert property (@(posedge clk) sync_reject_on (large_abort) (large_a |-> ##[1:300] large_b)) begin
    if (large_abort) large_reject_pass++;
  end
  else if (large_abort) large_reject_fail++;
  assert property (@(posedge clk) disable iff (large_disable)
                   sync_accept_on (large_abort) (large_a |-> ##[1:300] large_b)) begin
    if (large_abort) large_disable_accept_pass++;
  end
  else if (large_abort) large_disable_accept_fail++;

  initial begin
    @(negedge clk) large_a = 1;
    @(negedge clk) large_a = 1;
    @(negedge clk) begin
      large_a = 0;
      large_b = 1;
      large_abort = 1;
    end
    @(negedge clk) begin
      large_b = 0;
      large_abort = 0;
      `checkd(small_checked, 1);
      `checkd(large_pass, 2);
      `checkd(large_fail, 2);
      `checkd(large_cover, 2);
      `checkd(large_implication_at_b, 3);
      `checkd(large_accept_pass, 3);
      `checkd(large_accept_fail, 0);
      `checkd(large_reject_pass, 0);  // Other sims: 1
      `checkd(large_reject_fail, 3);  // Other sims: 2
      `checkd(large_disable_accept_pass, 3);
      `checkd(large_disable_accept_fail, 0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
