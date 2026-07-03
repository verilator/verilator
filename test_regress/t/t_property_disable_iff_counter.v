// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// IEEE 1800-2023 16.12: a disable iff true at ANY point of a multi-cycle
// attempt window disables it. A range delay ##[1:N] with N over the 256 unroll
// limit lowers to a counter-FSM backend (not a state-register chain), which had
// the same mid-window-disable hole as the register path
// (verilator/verilator#7792 follow-up). value never matches, so a live attempt
// fails at window end; skip pulses once mid-window and must abort the in-flight
// counter so the disabled assert does not fire.

module t (
    input clk
);
  int cyc = 0;
  wire trig = (cyc == 5);
  wire value = 1'b0;  // never matches -> attempt would fail at window end
  wire skip = (cyc == 50);  // single mid-window pulse

  int n_dis_fire = 0;
  int n_ctrl_fire = 0;

  // Range > 256 -> counter FSM. The cyc-5 attempt is hit by the skip pulse.
  assert property (@(posedge clk) disable iff (skip) trig |-> ##[1:300] value)
  else n_dis_fire <= n_dis_fire + 1;

  // Control: same property never disabled -> the cyc-5 attempt fails once.
  assert property (@(posedge clk) disable iff (1'b0) trig |-> ##[1:300] value)
  else n_ctrl_fire <= n_ctrl_fire + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 320) begin
      `checkd(n_dis_fire, 0);
      `checkd(n_ctrl_fire, 1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
