// DESCRIPTION: Verilator: FSMMULTI warning test
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

  a_state_t state_a;
  b_state_t state_b;

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

endmodule
