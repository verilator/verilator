// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic a,
    input logic b,
    input logic clk,
    output logic pipeline_enable,
    output logic [1:0] pipeline_out,
    output logic [2:0] result,
    output logic [2:0] partial_out
);
  assign result[0] = a;
  assign result[1] = b;
  assign result[2] = ^result[1:0];

  // verilator lint_off UNOPTFLAT
  logic [2:0] partial;
  assign partial[0] = a;
  assign partial[2] = partial[1] ^ b;
  assign partial_out = partial;
  // verilator lint_on UNOPTFLAT

  logic [1:0] pipeline;
  assign pipeline[0] = pipeline_enable;
  always_ff @(posedge clk) pipeline[1] <= pipeline[0];
  always_comb pipeline_enable = !pipeline[1];
  assign pipeline_out = pipeline;

  // Keep non-clocked writes conservative, as they can be part of a real cycle.
  // verilator lint_off UNOPTFLAT
  logic [1:0] non_dfg_cycle;
  assign non_dfg_cycle[0] = !non_dfg_cycle[1];
  always_latch if (a) non_dfg_cycle[1] = non_dfg_cycle[0];
  // verilator lint_on UNOPTFLAT

  // A value-change sensitivity is not a clocked-state boundary.
  // verilator lint_off UNOPTFLAT
  logic [1:0] event_cycle;
  assign event_cycle[0] = !event_cycle[1];
  always @(a) event_cycle[1] = event_cycle[0];
  // verilator lint_on UNOPTFLAT
endmodule
