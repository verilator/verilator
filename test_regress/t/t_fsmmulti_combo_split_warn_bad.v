// DESCRIPTION: Verilator: FSMMULTI warning test for duplicate split FSM transition blocks
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk
);

  /* verilator lint_off MULTIDRIVEN */
  typedef enum logic [1:0] {
    S0, S1
  } state_t;

  state_t state_q;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = S1;
      default: state_d = S0;
    endcase
  end

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = S1;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
  /* verilator lint_on MULTIDRIVEN */

endmodule
