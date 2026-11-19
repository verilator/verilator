// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Names the pass generates do not clash with each other or with names in the design
module top_module (
    input clk,
    output logic [7:0] o_elem,
    output logic [7:0] o_var,
    output logic [7:0] o_gen,
    output logic [7:0] o_scoped,
    output logic [7:0] o_design
);
  logic [7:0] mem[4] = '{default: 0};
  logic [7:0] mem_2 = 0;
  logic [7:0] x_g_0 = 0;
  logic [7:0] dpiHooked_mem_2 = 0;
  always_ff @(posedge clk) begin
    for (int i = 0; i < 4; ++i) mem[i] <= mem[i] + 8'(i + 1);
    mem_2 <= mem_2 + 8'd5;
    x_g_0 <= x_g_0 + 8'd7;
    dpiHooked_mem_2 <= dpiHooked_mem_2 + 8'd9;
  end
  for (genvar i = 0; i < 1; ++i) begin : g
    logic [7:0] x = 0;
    always_ff @(posedge clk) x <= x + 8'd1;
  end
  assign o_elem = mem[2];
  assign o_var = mem_2;
  assign o_gen = g[0].x;
  assign o_scoped = x_g_0;
  assign o_design = dpiHooked_mem_2;

  final $write("*-* All Finished *-*\n");
endmodule
