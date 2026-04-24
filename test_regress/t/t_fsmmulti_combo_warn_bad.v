// DESCRIPTION: Verilator: FSMMULTI warning test for combinational transition blocks
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk
);

  typedef enum logic [1:0] {
    A0, A1
  } a_state_t;

  typedef enum logic [1:0] {
    B0, B1
  } b_state_t;

  a_state_t state_a_q;
  a_state_t state_a_d;
  b_state_t state_b_q;
  b_state_t state_b_d;

  always_comb begin
    state_a_d = state_a_q;
    state_b_d = state_b_q;
    case (state_a_q)
      A0: state_a_d = A1;
      default: state_a_d = A0;
    endcase
    case (state_b_q)
      B0: state_b_d = B1;
      default: state_b_d = B0;
    endcase
  end

  always_ff @(posedge clk) begin
    state_a_q <= state_a_d;
  end

  always_ff @(posedge clk) begin
    state_b_q <= state_b_d;
  end

endmodule
