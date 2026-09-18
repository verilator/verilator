// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// --vpi-lazy: a copy may only fold onto a group TARGET, never onto a group temp.
//
// A group's map of solely-written variables covers its temps too. 'o' is a module port, so
// it never becomes a target, but the group's block is its only writer, which makes it a
// solely-written temp; 'mix' reads it, which keeps it in the pruned cone and gives it a
// temp shadow. That shadow is refreshed only by 'mix's reconstruct function and
// has none of its own, so a copy folded onto it reads a shadow nothing refreshes: a stale
// value through VPI, with no error anywhere.

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

// Not inlined, so 'o' stays a port and can never be a reconstruction target.
module tempsrc (
  input logic [31:0] i,
  output logic [31:0] o,
  output logic [31:0] obs
);
  /* verilator no_inline_module */

  logic [31:0] mix;
  logic [31:0] cpy_a;
  logic [31:0] cpy_c;

  // Multi-statement, so 'o' is a temp of this group and 'mix' its only target
  always_comb begin
    o = i ^ 32'h5a5a_0000;
    mix = o + 32'd3;
  end

  // One-statement copies of that temp, in both group shapes: a fold must refuse each
  always_comb cpy_a = o;
  assign cpy_c = o;

  assign obs = (mix ^ cpy_a) + cpy_c;

endmodule
