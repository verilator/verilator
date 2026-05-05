// DESCRIPTION: Verilator: FSM coverage ignores grouped unsupported FSM extraction patterns
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Group unsupported extraction shapes that must compile and run cleanly while
// emitting no FSM coverage points at all.

module fsm_caseitem_varrhs_bad (
    input logic clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic start;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;
  state_t other_d;

  initial begin
    start = 1'b0;
    cyc = 0;
    other_d = S1;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) start <= 1'b0;
  end

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = other_d;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module fsm_caseitem_then_nonconst_bad (
    input logic clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  logic sel;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;
  state_t other_d;

  initial begin
    sel = 1'b0;
    cyc = 0;
    other_d = S1;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
  end

  always_comb begin
    state_d = state_q;
    /* verilator lint_off CASEINCOMPLETE */
    case (state_q)
      S0: state_d = sel ? other_d : S1;
    endcase
    /* verilator lint_on CASEINCOMPLETE */
  end

  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module fsm_caseitem_else_nonconst_bad (
    input logic clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  logic sel;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;
  state_t other_d;

  initial begin
    sel = 1'b0;
    cyc = 0;
    other_d = S1;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
  end

  always_comb begin
    state_d = state_q;
    /* verilator lint_off CASEINCOMPLETE */
    case (state_q)
      S0: state_d = sel ? S1 : other_d;
    endcase
    /* verilator lint_on CASEINCOMPLETE */
  end

  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module fsm_oneblock_then_bad (
    input logic clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic rst;
  logic sel;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  initial begin
    rst = 1'b1;
    sel = 1'b0;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
  end

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = sel ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    state_q <= rst ? (sel ? S0 : S1) : state_d;
  end
endmodule

module fsm_oneblock_else_bad (
    input logic clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic rst;
  logic sel;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  initial begin
    rst = 1'b1;
    sel = 1'b0;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
  end

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = sel ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    state_q <= rst ? S0 : (sel ? S1 : state_d);
  end
endmodule

module fsm_combo_sel_expr_bad (
    input logic clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic rst;
  logic start;
  integer cyc;
  state_t state_q  /*verilator fsm_reset_arc*/;
  state_t state_d;

  initial begin
    rst = 1'b1;
    start = 1'b0;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) start <= 1'b0;
  end

  always_comb begin
    state_d = state_q;
    case (state_q + 1)
      S0: state_d = start ? S1 : S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state_q <= S0;
    end
    else begin
      state_q <= state_d;
    end
  end
endmodule

module fsm_normalized_if_noelse_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic rst;
  logic start;
  integer cyc;
  state_t state_q  /*verilator fsm_reset_arc*/;
  state_t state_d;

  initial begin
    rst = 1'b1;
    start = 1'b0;
    cyc = 0;
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) start <= 1'b0;
  end
  always_comb begin
    state_d = state_q;
    case (state_q)
      S0:
      if (start);
      else state_d = S1;
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_normalized_if_then_nonconst_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic sel;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;
  state_t tmp_a;
  state_t tmp_b;
  state_t other_d;

  initial begin
    sel = 1'b0;
    cyc = 0;
    other_d = S2;
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
  end
  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: begin
        if (sel) tmp_a = other_d;
        else tmp_b = S1;
        state_d = tmp_a;
      end
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module fsm_normalized_if_else_nonconst_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic sel;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;
  state_t tmp_a;
  state_t tmp_b;
  state_t other_d;

  initial begin
    sel = 1'b0;
    cyc = 0;
    other_d = S2;
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
  end
  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: begin
        if (sel) tmp_a = S1;
        else tmp_b = other_d;
        state_d = tmp_a;
      end
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module fsm_normalized_if_temp_mismatch_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic sel;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;
  state_t tmp_a;
  state_t tmp_b;

  initial begin
    sel = 1'b0;
    cyc = 0;
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
  end
  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: begin
        if (sel) tmp_a = S1;
        else tmp_b = S2;
        state_d = tmp_a;
      end
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module fsm_normalized_if_then_state_else_other_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic sel;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;
  state_t tmp_a;

  initial begin
    sel = 1'b0;
    cyc = 0;
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
  end
  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: begin
        if (sel) state_d = S1;
        else tmp_a = S2;
        state_d = tmp_a;
      end
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module fsm_normalized_if_same_temp_nofollow_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic sel;
  logic aux;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;
  state_t tmp_a;

  initial begin
    sel = 1'b0;
    cyc = 0;
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
  end
  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: begin
        if (sel) begin
          tmp_a = S1;
          aux = 1'b1;
        end
        else begin
          tmp_a = S2;
          aux = 1'b0;
        end
      end
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module fsm_normalized_if_follow_nonvar_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic sel;
  logic aux;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;
  state_t tmp_a;

  initial begin
    sel = 1'b0;
    cyc = 0;
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
  end
  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: begin
        if (sel) begin
          tmp_a = S1;
          aux = 1'b1;
        end
        else begin
          tmp_a = S2;
          aux = 1'b0;
        end
        // Final follow-up is not a plain var-to-var state assignment.
        aux = (tmp_a == S1);
      end
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module fsm_normalized_if_follow_wrongfrom_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic sel;
  logic aux;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;
  state_t tmp_a;
  state_t other_d;

  initial begin
    sel = 1'b0;
    cyc = 0;
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
  end
  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: begin
        if (sel) begin
          tmp_a = S1;
          aux = 1'b1;
        end
        else begin
          tmp_a = S2;
          aux = 1'b0;
        end
        // Final follow-up reads from the wrong source temp.
        state_d = other_d;
      end
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module fsm_normalized_if_follow_wronglhs_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic sel;
  logic aux;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;
  state_t tmp_a;
  state_t other_d;

  initial begin
    sel = 1'b0;
    cyc = 0;
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
  end
  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: begin
        if (sel) begin
          tmp_a = S1;
          aux = 1'b1;
        end
        else begin
          tmp_a = S2;
          aux = 1'b0;
        end
        // Final follow-up writes the wrong lhs instead of state_d.
        other_d = tmp_a;
      end
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module fsm_case_next_wrongrhs_bad (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic rst;
  logic start;
  integer cyc;
  state_t state_q  /*verilator fsm_reset_arc*/;
  state_t state_d;
  state_t other_d;

  initial begin
    rst = 1'b1;
    start = 1'b0;
    cyc = 0;
    other_d = S1;
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) start <= 1'b0;
  end
  always_comb begin
    state_d = other_d;
    case (state_d)
      S0: state_d = start ? S1 : S2;
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_forced_wide_bad (
    input logic clk
);

  integer cyc;
  logic rst;
  logic [30:0] state  /*verilator fsm_state*/;

  initial begin
    cyc = 0;
    rst = 1'b1;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 6) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state <= 31'd0;
    end
    else begin
      case (state)
        31'd0: state <= 31'd1;
        31'd1: state <= 31'd2;
        default: state <= 31'd0;
      endcase
    end
  end

endmodule

module fsm_reset_commit_mismatch_bad (
    input logic clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic rst;
  logic start;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t other_q;
  state_t state_d;

  initial begin
    rst = 1'b1;
    start = 1'b0;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) start <= 1'b0;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = start ? S1 : S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) other_q <= S0;
    else state_q <= state_d;
  end

endmodule

module fsm_reset_then_bad (
    input logic clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic rst;
  logic sel;
  integer cyc;
  state_t state_q  /*verilator fsm_state*/;
  state_t state_d;

  initial begin
    rst = 1'b1;
    sel = 1'b0;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = sel ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= sel ? S0 : S1;
    else state_q <= state_d;
  end

endmodule

module t (
    input logic clk
);

  integer cyc;

  fsm_caseitem_varrhs_bad caseitem_varrhs_bad_u (.clk(clk));
  fsm_caseitem_then_nonconst_bad caseitem_then_nonconst_bad_u (.clk(clk));
  fsm_caseitem_else_nonconst_bad caseitem_else_nonconst_bad_u (.clk(clk));
  fsm_oneblock_then_bad oneblock_then_bad_u (.clk(clk));
  fsm_oneblock_else_bad oneblock_else_bad_u (.clk(clk));
  fsm_combo_sel_expr_bad combo_sel_expr_bad_u (.clk(clk));
  fsm_normalized_if_noelse_bad normalized_if_noelse_bad_u (.clk(clk));
  fsm_normalized_if_then_nonconst_bad normalized_if_then_nonconst_bad_u (.clk(clk));
  fsm_normalized_if_else_nonconst_bad normalized_if_else_nonconst_bad_u (.clk(clk));
  fsm_normalized_if_temp_mismatch_bad normalized_if_temp_mismatch_bad_u (.clk(clk));
  fsm_normalized_if_then_state_else_other_bad normalized_if_then_state_else_other_bad_u (.clk(clk));
  fsm_normalized_if_same_temp_nofollow_bad normalized_if_same_temp_nofollow_bad_u (.clk(clk));
  fsm_normalized_if_follow_nonvar_bad normalized_if_follow_nonvar_bad_u (.clk(clk));
  fsm_normalized_if_follow_wrongfrom_bad normalized_if_follow_wrongfrom_bad_u (.clk(clk));
  fsm_normalized_if_follow_wronglhs_bad normalized_if_follow_wronglhs_bad_u (.clk(clk));
  fsm_case_next_wrongrhs_bad case_next_wrongrhs_bad_u (.clk(clk));
  fsm_forced_wide_bad forced_wide_bad_u (.clk(clk));
  fsm_reset_commit_mismatch_bad reset_commit_mismatch_bad_u (.clk(clk));
  fsm_reset_then_bad reset_then_bad_u (.clk(clk));

  initial cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
