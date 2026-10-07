// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A sized array of bins needs a positive integral size (IEEE 1800-2023 19.5.1), and two-state
// range bounds, as do bins with a 'with' filter, of which '$' may only be a whole bound (6.20.7)

module t;
  logic [3:0] value;
  localparam UNBOUNDED = $;

  covergroup cg;
    cp: coverpoint value {
      bins zero[0] = {[0 : 3]};  // <--- Bad: zero
      bins negative[-1] = {[0 : 3]};  // <--- Bad: negative
      bins fraction[1.5] = {[0 : 3]};  // <--- Bad: not integral
      bins four_state[2] = {[4'b000x : 4'hf]};  // <--- Bad: x bound
      bins four_state_with = {[4'b000x : 4'hf]} with (1);  // <--- Bad: x bound
      bins param_size[UNBOUNDED] = {[0 : 3]};  // <--- Bad: '$'
      bins param_value[2] = {UNBOUNDED};  // <--- Bad: '$'
    }
  endgroup

  // A cross bin's 'matches' count is a positive integer, or '$' (IEEE 1800-2023 19.6.1.2)
  covergroup cg_matches;
    aa: coverpoint value;
    bb: coverpoint value;
    xx: cross aa, bb{
      bins zero = xx with (aa == bb) matches 0;  // <--- Bad: zero
      bins negative = xx with (aa == bb) matches -1;  // <--- Bad: negative
      bins fraction = xx with (aa == bb) matches 1.5;  // <--- Bad: not integral
      bins four_state = xx with (aa == bb) matches 2'b1x;  // <--- Bad: x
      bins param_all = xx with (aa == bb) matches UNBOUNDED;  // '$'
    }
  endgroup

  cg cg_inst = new;
  cg_matches matches_inst = new;
  initial $finish;
endmodule
