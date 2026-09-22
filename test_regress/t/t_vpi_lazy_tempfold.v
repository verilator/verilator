// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Copies may fold only onto group targets, never group temporaries.

module t (
  input logic clk,
  input logic rst,
  input logic [31:0] in,
  output logic [31:0] out
);

  logic [31:0] acc;
  logic [31:0] src_o;
  logic [31:0] src_obs;

  always_ff @(posedge clk) acc <= rst ? 32'd0 : acc + in;

  tempsrc u_src(.i(acc), .o(src_o), .obs(src_obs));

  assign out = src_o ^ src_obs;

endmodule

// Not inlined so 'o' remains a port.
module tempsrc (
  input logic [31:0] i,
  output logic [31:0] o,
  output logic [31:0] obs
);
  /* verilator no_inline_module */

  logic [31:0] mix;
  logic [31:0] cpy_a;
  logic [31:0] cpy_c;

  // 'o' is a group temporary; 'mix' is the target.
  always_comb begin
    o = i ^ 32'h5a5a_0000;
    mix = o + 32'd3;
  end

  // Both copy shapes must refuse the temporary.
  always_comb cpy_a = o;
  assign cpy_c = o;

  assign obs = (mix ^ cpy_a) + cpy_c;

endmodule
