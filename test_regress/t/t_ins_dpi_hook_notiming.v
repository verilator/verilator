// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Hooks without timing: the harness drives the clock and the trigger
interface data_if;
  logic [7:0] data;
endinterface

interface outer_if;
  data_if inner ();
endinterface

module top_module (
    input clk,
    output logic [7:0] o_mod,
    output logic [7:0] o_if,
    output logic [7:0] o_nested,
    output logic [7:0] o_gen
);
  logic [7:0] cnt = 0;
  logic [7:0] mreg = 0;
  always_ff @(posedge clk) cnt <= cnt + 8'd1;
  always_ff @(posedge clk) mreg <= cnt;

  data_if di ();
  outer_if oi ();
  always_comb di.data = cnt;
  always_comb oi.inner.data = cnt;
  for (genvar g = 0; g < 2; ++g) begin : lane
    data_if gi ();
    always_comb gi.data = cnt;
  end

  assign o_mod = mreg;
  assign o_if = di.data;
  assign o_nested = oi.inner.data;
  assign o_gen = lane[1].gi.data;

  final $write("*-* All Finished *-*\n");
endmodule
