// DESCRIPTION: Verilator: FSM coverage warns on non-clocked always near-FSM shapes
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module warn_edge (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_reset_arc*/;
  state_t state_d;

  // Plain edge-sensitive next-state logic should warn even when the selector
  // is the canonical state_q form.
  always @(posedge clk) begin
    state_d = state_q;
    case (state_q)
      S0: state_d = start ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module warn_case_next (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_reset_arc*/;
  state_t state_d;

  // Plain always also warns for the near-supported case(state_d) style.
  always @(posedge clk) begin
    state_d = state_q;
    case (state_d)
      S0: state_d = start ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module warn_default_incl (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_reset_arc*/  /*verilator fsm_arc_include_cond*/;
  state_t state_d;

  // default becomes supported only because include_cond is set, but the block
  // still warns because it is a plain edge-sensitive always.
  always @(posedge clk) begin
    state_d = state_q;
    case (state_q)
      default: state_d = S0;
      S0: state_d = start ? state_q : state_q;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module t;
  logic clk;
  logic rst;
  logic start;

  warn_edge warn_edge_u (.*);
  warn_case_next warn_case_next_u (.*);
  warn_default_incl warn_default_incl_u (.*);
endmodule
