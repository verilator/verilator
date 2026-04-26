// DESCRIPTION: Verilator: FSM conditional transition rejects unknown enum constants on either ternary arm
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module unknown_then (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  logic sel;
  state_t state_q /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    case (state_q)
      /* verilator lint_off ENUMVALUE */
      S0: state_d = sel ? 2'd3 : S1;
      /* verilator lint_on ENUMVALUE */
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module unknown_else (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  logic sel;
  state_t state_q /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    case (state_q)
      /* verilator lint_off ENUMVALUE */
      S0: state_d = sel ? S1 : 2'd3;
      /* verilator lint_on ENUMVALUE */
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module t;
  logic clk;
  unknown_then unknown_then_u(.clk(clk));
  unknown_else unknown_else_u(.clk(clk));
endmodule
