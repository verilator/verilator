// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Per-attempt abort outcomes over a windowed implication.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  bit large_a = 0, large_b = 0, large_abort = 0, large_disable = 0;
  int large_accept_pass = 0, large_accept_fail = 0;
  int large_reject_pass = 0, large_reject_fail = 0;
  int large_disable_accept_pass = 0, large_disable_accept_fail = 0;

  initial $assertpasson;

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
      `checkd(large_accept_pass, 3);
      `checkd(large_accept_fail, 0);
      `checkd(large_reject_pass, 0);  // Other simulator: 1
      `checkd(large_reject_fail, 3);  // Other simulator: 2
      `checkd(large_disable_accept_pass, 3);
      `checkd(large_disable_accept_fail, 0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
