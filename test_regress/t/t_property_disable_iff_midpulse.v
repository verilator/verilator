// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// IEEE 1800-2023 16.12: a disable iff condition true at ANY point of a
// multi-cycle attempt window disables that attempt, not only when held
// continuously (verilator/verilator#7792 follow-up to #7841). skip is a plain
// non-$sampled, non-constant signal pulsed true for a single cycle in the
// MIDDLE of the ##10 window. value is low only at the attempt's match cycle, so
// exactly one attempt would fail; the mid-window skip pulse must disable it.
// Pre-fix the in-flight NFA states were not zeroed on a mid-window pulse, so the
// disabled assert fired; the control proves the same attempt fails when enabled.

module t (
    input clk
);
  int cyc = 0;
  wire value = (cyc != 10);  // low only at the cyc-0 attempt's match cycle
  wire skip = (cyc == 5);  // single-cycle pulse, mid-window of [0..10]

  int n_dis_fire = 0;
  int n_ctrl_fire = 0;

  // Mid-window-pulse disable: the cyc-0 attempt (matches at cyc 10, where value
  // is low -> would fail) must be disabled by the skip pulse at cyc 5.
  assert property (@(posedge clk) disable iff (skip) (##10 value))
  else n_dis_fire <= n_dis_fire + 1;

  // Control: same property always enabled -> the cyc-0 attempt fails once.
  assert property (@(posedge clk) disable iff (1'b0) (##10 value))
  else n_ctrl_fire <= n_ctrl_fire + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 20) begin
      `checkd(n_dis_fire, 0);
      `checkd(n_ctrl_fire, 1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
