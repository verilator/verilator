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
  logic a_high = 1'b1, b_high = 1'b1, c_high = 1'b1;
  int wide_pass_q[$], wide_strong_pass_q[$];

  // Wide range with multi-operand pure propp -- exercises the shared
  // $sampled(propp) hoist path; pre-fix would clone propp 33 times.
  assert property (@(posedge clk) always[1: 33] (a_high && b_high && c_high))
    wide_pass_q.push_back(cyc);

  // Wide strong s_always over the same expression (in-window matches weak).
  assert property (@(posedge clk) s_always[1: 33] (a_high && b_high && c_high))
    wide_strong_pass_q.push_back(cyc);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 49) begin
      // Constant-true [1:33]: K=0..16 succeed at cyc K+33 = 33..49.
      `checkd(wide_pass_q.size(), 17);
      `checkd(wide_pass_q[0], 33);
      `checkd(wide_pass_q[$], 49);
      `checkd(wide_strong_pass_q.size(), 17);
      `checkd(wide_strong_pass_q[0], 33);
      `checkd(wide_strong_pass_q[$], 49);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
