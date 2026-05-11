// DESCRIPTION: Verilator: same-FSM combo multi-case warning test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic rst
);

  typedef enum logic [1:0] {
    S0,
    S1,
    S2
  } state_t;

  state_t state_q;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = S1;
      default: ;
    endcase
    case (state_q)
      S1: state_d = S2;
      default: ;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end

endmodule
