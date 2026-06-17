// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic a_high = 1'b1;
  logic a_low = 1'b0;

  int low_s_fail_q[$];
  int low_w_fail_q[$];

  // A new attempt starts every tick, so the last hi attempts still have an open
  // [2:5] window when the trace ends. Even though a_high is constantly true,
  // those unfinished attempts report a liveness failure; Verilator OR-reduces
  // them into one end-of-simulation error. (Questa 2022.3: 6 earlier attempts
  // complete, the 5 youngest fire the strong else at $finish.)
  assert property (@(posedge clk) s_always [2:5] a_high);
  // Weak always makes no end-of-trace obligation: silent.
  assert property (@(posedge clk) always [2:5] a_high);

  // Constant-false fails at the first window tick: a safety violation reported
  // identically by weak and strong (the strong-only liveness affects just the
  // still-open tail). Verilator counts 9 each at cyc 10. (Questa reads 8 -- a
  // same-timestep else-vs-read ordering difference, not a semantic one.)
  assert property (@(posedge clk) s_always [2:5] a_low)
    else low_s_fail_q.push_back(cyc);
  assert property (@(posedge clk) always [2:5] a_low)
    else low_w_fail_q.push_back(cyc);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      `checkd(low_s_fail_q.size(), low_w_fail_q.size());
      `checkd(low_w_fail_q.size(), 9);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
