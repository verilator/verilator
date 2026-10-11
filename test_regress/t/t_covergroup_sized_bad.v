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

  cg cg_inst = new;
  initial $finish;
endmodule
