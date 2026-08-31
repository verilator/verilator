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
  wire a_drop = cyc != 1025;
  int nested_or_fail_q[$];
  int negated_fail_q[$];
  int narrow_fail_q[$];
  int wide_fail_q[$];
  int wide_pass_q[$];
  int wide_ring_pass_q[$];

  // Wide range with multi-operand pure propp -- exercises the shared
  // $sampled(propp) hoist path; pre-fix would clone propp 33 times.
  assert property (@(posedge clk) always[1: 33] (a_high && b_high && c_high))
    wide_pass_q.push_back(cyc);

  // Wide range exercises the fixed-delay ring-buffer path
  assert property (@(posedge clk) always[1:1025] (a_high && b_high && c_high))
    wide_ring_pass_q.push_back(cyc);

  // All 1025 live threads fail together when a_drop falls.
  assert property (@(posedge clk) always[1:1025] a_drop)
  else wide_fail_q.push_back(cyc);

  // A one-cycle remainder uses a scalar state instead of a ring.
  assert property (@(posedge clk) always[1:2] a_drop)
  else narrow_fail_q.push_back(cyc);

  // A nested always may fail without rejecting a successful property or.
  assert property (@(posedge clk) (always [0:1] 1'b0) or a_high)
  else nested_or_fail_q.push_back(cyc);

  // The same drop passes a negated always; it must not replay fail actions.
  assert property (@(posedge clk) not always[1:1025] a_drop)
  else negated_fail_q.push_back(cyc);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 49) begin
      `checkd(wide_pass_q.size(), 16);
      `checkd(wide_pass_q[0], 34);
      `checkd(wide_pass_q[$], 49);
    end
    if (cyc == 1041) begin
      // Constant-true [1:1025]: K=0..15 succeed at cyc K+1025 and push the updated cyc.
      `checkd(wide_ring_pass_q.size(), 16);
      `checkd(wide_ring_pass_q[0], 1026);
      `checkd(wide_ring_pass_q[$], 1041);
      `checkd(wide_fail_q.size(), 1025);
      `checkd(wide_fail_q[0], 1026);
      `checkd(wide_fail_q[$], 1026);
      `checkd(narrow_fail_q.size(), 2);
      `checkd(narrow_fail_q[0], 1026);
      `checkd(narrow_fail_q[$], 1026);
      `checkd(nested_or_fail_q.size(), 0);
      `checkd(negated_fail_q.size(), 0);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
