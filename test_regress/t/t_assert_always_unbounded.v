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
  logic a_drop = 1'b1;

  // Weak always [m:$] is a pure safety property: it has no end-of-trace
  // obligation, so it can only fail (else fires), once per failing tick.
  int high_fail_q[$];
  int low0_fail_q[$];
  int low2_fail_q[$];
  int drop_fail_q[$];

  // Constant-true input: never fails at any tick.
  assert property (@(posedge clk) always [2:$] a_high) else high_fail_q.push_back(cyc);

  // Constant-false input, m=0: fails at every observed tick.
  assert property (@(posedge clk) always [0:$] a_low) else low0_fail_q.push_back(cyc);

  // Constant-false input, m=2: fails at every tick once the window is live.
  assert property (@(posedge clk) always [2:$] a_low) else low2_fail_q.push_back(cyc);

  // a_drop is high then drops at cyc 5 and stays low: deterministic single
  // transition, so Verilator and Questa agree on the failing ticks exactly.
  assert property (@(posedge clk) always [2:$] a_drop) else drop_fail_q.push_back(cyc);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc >= 4) a_drop <= 1'b0;
    if (cyc == 19) begin
      // Counts pinned to Verilator (NFA per-cycle reject). For all-fail windows
      // Questa is one lower (it does not fire the end-of-sim tick); see the sva
      // lessons "multi-cycle end-of-simulation offset" note.
      `checkd(high_fail_q.size(), 0);  // Questa: 0
      `checkd(low0_fail_q.size(), 20);  // Questa: 19
      `checkd(low2_fail_q.size(), 18);  // Questa: 17
      `checkd(drop_fail_q[0], 5);  // first fail tick: a_drop sampled low from cyc 5
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
