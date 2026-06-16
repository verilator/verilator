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
  logic a_low  = 1'b0;

  int low_s_fail_q[$];
  int low_w_fail_q[$];

  as_liveness: assert property (@(posedge clk) s_always [2:5] a_high);
  as_weak: assert property (@(posedge clk) always [2:5] a_high);

  as_low_s: assert property (@(posedge clk) s_always [2:5] a_low)
    ; else low_s_fail_q.push_back(cyc);
  as_low_w: assert property (@(posedge clk) always [2:5] a_low)
    ; else low_w_fail_q.push_back(cyc);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 4) begin
      `checkd(low_s_fail_q.size(), 3);
      `checkd(low_w_fail_q.size(), 3);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
