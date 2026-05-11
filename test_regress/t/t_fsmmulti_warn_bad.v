// DESCRIPTION: Verilator: FSMMULTI warning test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk
);

  typedef enum logic [1:0] {
    A0,
    A1
  } a_state_t;

  typedef enum logic [1:0] {
    B0,
    B1
  } b_state_t;

  typedef enum logic [1:0] {
    C0,
    C1
  } c_state_t;

  typedef enum logic [1:0] {
    D0,
    D1
  } d_state_t;

  a_state_t state_a;
  b_state_t state_b;
  c_state_t state_c;
  d_state_t state_d;

  always_ff @(posedge clk) begin
    case (state_a)
      A0: state_a <= A1;
      default: state_a <= A0;
    endcase
    case (state_b)
      B0: state_b <= B1;
      default: state_b <= B0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (state_c == C0) state_c <= C1;
    else if (state_c == C1) state_c <= C0;

    if (state_d == D0) state_d <= D1;
    else if (state_d == D1) state_d <= D0;
  end

endmodule
