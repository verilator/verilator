// DESCRIPTION: Verilator: FSM coverage ignores unsupported if/else-chain dispatch
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module fsm_if_mixed_vars_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  state_t other_q;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    if (state_q == S0) state_d = S1;
    else if (other_q == S1) state_d = S2;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_one_branch_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    if (state_q == S0) state_d = S1;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_duplicate_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    if (state_q == S0) state_d = S1;
    else if (state_q == S0) state_d = S0;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_two_comparisons_bad (
    input logic clk,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    if ((state_q == S0) && (state_q == S1)) state_d = S2;
    else if (state_q == S1) state_d = S0;
  end

  always_ff @(posedge clk) state_q <= start ? state_d : state_q;
endmodule

module fsm_if_or_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    if ((state_q == S0) || (state_q == S1)) state_d = S2;
    else if (state_q == S2) state_d = S0;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_alias_guard_bad (
    input logic clk,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic idle_state;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    idle_state = (state_q == S0) && start;
    if (idle_state) state_d = S1;
    else if (state_q == S1) state_d = S2;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_ambiguous_alias_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic idle_state;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    idle_state = (state_q == S0);
    idle_state = (state_q == S1);
    idle_state = (state_q == S2);
    if (idle_state) state_d = S2;
    else if (state_q == S2) state_d = S0;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_missing_default_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    state_d = S0;
    if (state_d == S0) state_d = S1;
    else if (state_d == S1) state_d = S2;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_no_assign_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  logic flag;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    flag = 1'b0;
    state_d = state_q;
    if (state_q == S0) flag = 1'b1;
    else if (state_q == S1) state_d = S0;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_nonvar_compare_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    if ((state_q + 2'd0) == S0) state_d = S1;
    else if (state_q == S1) state_d = S0;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_var_rhs_compare_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    if (state_q == state_d) state_d = S1;
    else if (state_q == S1) state_d = S0;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_alias_other_state_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  logic idle_state;
  state_t state_q  /*verilator fsm_state*/;
  state_t other_q;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    idle_state = (state_q == S0);
    idle_state = (other_q == S0);
    if (idle_state) state_d = S1;
    else if (state_q == S1) state_d = S0;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_bit_or_bad (
    input logic clk,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    if ((state_q == S0) | start) state_d = S1;
    else if (state_q == S1) state_d = S2;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_reduction_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    if (&state_q) state_d = S1;
    else if (state_q == S1) state_d = S2;
    if (|state_q) state_d = S2;
    else if (state_q == S2) state_d = S0;
    if (^state_q) state_d = S0;
    else if (state_q == S0) state_d = S1;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module t (
    input logic clk,
    input logic start
);
  integer cyc;

  fsm_if_mixed_vars_bad mixed_vars_u (.clk(clk));
  fsm_if_one_branch_bad one_branch_u (.clk(clk));
  fsm_if_duplicate_bad duplicate_u (.clk(clk));
  fsm_if_two_comparisons_bad two_comparisons_u (.clk(clk), .start(start));
  fsm_if_or_bad or_u (.clk(clk));
  fsm_if_alias_guard_bad alias_guard_u (.clk(clk), .start(start));
  fsm_if_ambiguous_alias_bad ambiguous_alias_u (.clk(clk));
  fsm_if_missing_default_bad missing_default_u (.clk(clk));
  fsm_if_no_assign_bad no_assign_u (.clk(clk));
  fsm_if_nonvar_compare_bad nonvar_compare_u (.clk(clk));
  fsm_if_var_rhs_compare_bad var_rhs_compare_u (.clk(clk));
  fsm_if_alias_other_state_bad alias_other_state_u (.clk(clk));
  fsm_if_bit_or_bad bit_or_u (.clk(clk), .start(start));
  fsm_if_reduction_bad reduction_u (.clk(clk));

  initial cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 6) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
