// DESCRIPTION: Verilator: FSM coverage negative extraction test
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

module fsm_if_var_target_bad (
    input logic clk,
    input logic [1:0] dyn
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
    if (state_q == S0) state_d = state_t'(dyn);
    else if (state_q == S1) state_d = S2;
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
module fsm_if_else_chain_decode_bad (
    input logic clk,
    input logic [1:0] dyn
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  logic [1:0] code;

  // A decoder on the state, not next-state logic
  always_comb begin
    if (state_q == S0) code = 2'd3;
    else if (state_q == S1) code = 2'd1;
    else code = 2'd0;
  end

  always_ff @(posedge clk) state_q <= state_t'(dyn);
endmodule

module fsm_if_else_chain_var_target_bad (
    input logic clk,
    input logic [1:0] dyn
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    if (state_q == S0) state_d = S1;
    else if (state_q == S1) state_d = state_t'(dyn);
    else state_d = S0;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_else_chain_mixed_vars_bad (
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
    if (state_q == S0) state_d = S1;
    else if (other_q == S1) state_d = S2;
    else state_d = S0;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_else_chain_duplicate_bad (
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
    if (state_q == S0 && start) state_d = S1;
    else if (state_q == S0) state_d = S2;
    else state_d = S0;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_else_chain_one_branch_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  always_comb begin
    if (state_q == S0) state_d = S1;
    else state_d = S0;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_if_else_chain_or_bad (
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
    if ((state_q == S0) || (state_q == S1)) state_d = S2;
    else if (state_q == S2) state_d = S0;
    else state_d = S1;
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule
module fsm_if_else_chain_tail_decode_bad (
    input logic clk,
    input logic rst,
    input logic go
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q;
  state_t state_d;
  logic busy;

  // The tail folds to 'state_d = (state_q == S1) ? S2 : go ? S0 : S1', which
  // tests an input after the state
  always_comb begin
    busy = 1'b0;
    if (state_q == S0) begin
      state_d = S1;
      busy = 1'b1;
    end
    else if (state_q == S1) state_d = S2;
    else if (go) state_d = S0;
    else state_d = S1;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_if_else_chain_user_var_bad (
    input logic clk,
    input logic rst
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q;
  state_t state_d;
  state_t next_v;
  logic busy;

  // The chain assigns a user variable, not a lifted temporary, before the
  // next state
  always_comb begin
    busy = 1'b0;
    if (state_q == S0) begin
      next_v = S1;
      busy = 1'b1;
    end
    else if (state_q == S1) next_v = S2;
    else next_v = S0;
    state_d = next_v;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_direct_active_low_dynamic_reset_bad (
    input logic clk,
    input logic rst_n,
    input logic [1:0] dyn_reset
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
    else state_d = S0;
  end
  always_ff @(posedge clk or negedge rst_n) begin
    state_q <= rst_n ? state_d : state_t'(dyn_reset);
  end
endmodule
module fsm_positive_compound_reset_bad (
    input logic clk,
    input logic rst_n,
    input logic flush,
    input logic [1:0] ctrl,
    input logic go,
    input logic seed
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  // An active-low reset in the else branch is only recognized on a plain signal
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;
  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = S1;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst_n && !flush) state_q <= state_d;
    else state_q <= S0;
  end
  // The same with two statements per branch, so it isn't folded into '?:'
  state_t if_q  /*verilator fsm_state*/;
  state_t if_d;
  logic [1:0] count;
  always_comb begin
    if_d = if_q;
    case (if_q)
      S0: if_d = S1;
      S1: if_d = S2;
      default: if_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst_n && !flush) begin
      if_q <= if_d;
      count <= count + 1'b1;
    end
    else begin
      if_q <= S0;
      count <= '0;
    end
  end
  // A '?:' on a bit select is not a plain signal either
  state_t sel_q  /*verilator fsm_state*/;
  state_t sel_d;
  always_comb begin
    sel_d = sel_q;
    case (sel_q)
      S0: sel_d = S1;
      S1: sel_d = S2;
      default: sel_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    sel_q <= ctrl[1] ? sel_d : S0;
  end
  // An else branch that doesn't start with a constant assignment isn't an active-low
  // reset around the case
  state_t oneblock_q  /*verilator fsm_state*/;
  logic aux;
  always_ff @(posedge clk) begin
    if (go)
      case (oneblock_q)
        S0: oneblock_q <= S1;
        S1: oneblock_q <= S2;
        default: oneblock_q <= S0;
      endcase
    else begin
      aux <= seed;
      oneblock_q <= S0;
    end
  end
endmodule
module fsm_reg_enable_no_else_bad (
    input logic clk,
    input logic start
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
    else state_d = S0;
  end
  // An enable with no else is not a reset guard
  always_ff @(posedge clk) begin
    if (start) state_q <= state_d;
  end
endmodule
module fsm_case_guarded_bad (
    input logic clk,
    input logic [1:0] dyn
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;
  logic side;

  // Only S0 is supported: a guarded arm with another statement, or with a
  // non-constant target, is skipped
  always_comb begin
    state_d = state_q;
    side = 1'b0;
    case (state_q)
      S0: state_d = S1;
      S1:
      if (dyn[0]) begin
        state_d = S2;
        side = 1'b1;
      end
      S2: if (dyn[1]) state_d = state_t'(dyn);
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_case_guarded_nohold_bad (
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

  // The default is not 'state_d = state_q', so a guarded item that leaves
  // state_d unassigned does not hold; S1 is skipped
  always_comb begin
    state_d = S0;
    case (state_q)
      S0: state_d = S1;
      S1: if (start) state_d = S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module fsm_case_guarded_overwrite_bad (
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

  // The canonical default is overwritten before the case, so S1 is skipped
  always_comb begin
    state_d = state_q;
    state_d = S0;
    case (state_q)
      S0: state_d = S1;
      S1: if (start) state_d = S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) state_q <= state_d;
endmodule

module t (
    input logic clk
);

  typedef enum logic [2:0] {
    S0 = 3'd0,
    S1 = 3'd1,
    S2 = 3'd2
  } state_t;

  int cyc = 0;
  logic start = 1'b0;
  logic side = 1'b0;
  logic dyn_side = 1'b0;
  logic [2:0] dyn_case = 3'd7;
  state_t state  /*verilator fsm_state*/;

  fsm_if_mixed_vars_bad mixed_vars_u (.clk(clk));
  fsm_if_one_branch_bad one_branch_u (.clk(clk));
  fsm_if_duplicate_bad duplicate_u (.clk(clk));
  fsm_if_two_comparisons_bad two_comparisons_u (
      .clk(clk),
      .start(start)
  );
  fsm_if_or_bad or_u (.clk(clk));
  fsm_if_alias_guard_bad alias_guard_u (
      .clk(clk),
      .start(start)
  );
  fsm_if_ambiguous_alias_bad ambiguous_alias_u (.clk(clk));
  fsm_if_missing_default_bad missing_default_u (.clk(clk));
  fsm_if_no_assign_bad no_assign_u (.clk(clk));
  fsm_if_nonvar_compare_bad nonvar_compare_u (.clk(clk));
  fsm_if_var_rhs_compare_bad var_rhs_compare_u (.clk(clk));
  fsm_if_var_target_bad var_target_u (
      .clk(clk),
      .dyn(dyn_case[1:0])
  );
  fsm_if_alias_other_state_bad alias_other_state_u (.clk(clk));
  fsm_if_bit_or_bad bit_or_u (
      .clk(clk),
      .start(start)
  );
  fsm_if_reduction_bad reduction_u (.clk(clk));
  fsm_if_else_chain_decode_bad else_chain_decode_u (
      .clk(clk),
      .dyn(dyn_case[1:0])
  );
  fsm_if_else_chain_var_target_bad else_chain_var_target_u (
      .clk(clk),
      .dyn(dyn_case[1:0])
  );
  fsm_if_else_chain_mixed_vars_bad else_chain_mixed_vars_u (.clk(clk));
  fsm_if_else_chain_duplicate_bad else_chain_duplicate_u (
      .clk(clk),
      .start(start)
  );
  fsm_if_else_chain_one_branch_bad else_chain_one_branch_u (.clk(clk));
  fsm_if_else_chain_or_bad else_chain_or_u (.clk(clk));
  fsm_if_else_chain_tail_decode_bad else_chain_tail_decode_u (
      .clk(clk),
      .rst(cyc == 0),
      .go(start)
  );
  fsm_if_else_chain_user_var_bad else_chain_user_var_u (
      .clk(clk),
      .rst(cyc == 0)
  );
  fsm_direct_active_low_dynamic_reset_bad active_low_dynamic_reset_u (
      .clk(clk),
      .rst_n(cyc != 0),
      .dyn_reset(dyn_case[1:0])
  );
  fsm_positive_compound_reset_bad positive_compound_reset_u (
      .clk(clk),
      .rst_n(cyc != 0),
      .flush(start),
      .ctrl(cyc[1:0]),
      .go(start),
      .seed(cyc[0])
  );
  fsm_reg_enable_no_else_bad reg_enable_no_else_u (
      .clk(clk),
      .start(start)
  );
  fsm_case_guarded_bad case_guarded_u (
      .clk(clk),
      .dyn(dyn_case[1:0])
  );
  fsm_case_guarded_nohold_bad case_guarded_nohold_u (
      .clk(clk),
      .start(start)
  );
  fsm_case_guarded_overwrite_bad case_guarded_overwrite_u (
      .clk(clk),
      .start(start)
  );

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) dyn_side <= 1'b1;
    dyn_case <= {2'b11, dyn_side};
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // The grouped S0/dyn_case arm keeps the supported S0 baseline while the
  // non-constant case item is skipped. The S1 and default arms are
  // deliberately unsupported extractor shapes: one has two meaningful
  // statements, the other writes a different lhs first. Coverage should ignore
  // those arcs rather than guessing.
  always_ff @(posedge clk) begin
    if (cyc == 0) begin
      state <= S0;
    end
    else begin
      case (state)
        S0, state_t'(dyn_case): state <= S1;
        S1: begin
          side <= ~side;
          state <= S2;
        end
        default: begin
          side <= 1'b0;
          state <= S0;
        end
      endcase
    end
  end

endmodule
