// DESCRIPTION: Verilator: FSM coverage ignores grouped unsupported transition-shape patterns
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

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
  state_t state_q /*verilator fsm_state*/;
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
  state_t state_q /*verilator fsm_state*/;
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
  state_t state_q /*verilator fsm_state*/;
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
  state_t state_q /*verilator fsm_state*/;
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
  state_t state_q /*verilator fsm_state*/;
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
  state_t state_q /*verilator fsm_reset_arc*/;
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
    end else begin
      state_q <= state_d;
    end
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

  initial cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
