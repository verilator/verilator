// DESCRIPTION: Verilator: FSMMULTI warning disabled without --coverage-fsm
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  typedef enum logic [1:0] {
    A0 = 2'd0,
    A1 = 2'd1,
    A2 = 2'd2
  } state_a_t;

  typedef enum logic [1:0] {
    B0 = 2'd0,
    B1 = 2'd1,
    B2 = 2'd2
  } state_b_t;

  logic clk;
  logic rst;
  state_a_t a_state;
  state_b_t b_state;

  always_ff @(posedge clk) begin
    if (rst) begin
      a_state <= A0;
      b_state <= B0;
    end
    else begin
      case (a_state)
        A0: a_state <= A1;
        A1: a_state <= A2;
        default: a_state <= A0;
      endcase
      case (b_state)
        B0: b_state <= B1;
        B1: b_state <= B2;
        default: b_state <= B0;
      endcase
    end
  end
endmodule
