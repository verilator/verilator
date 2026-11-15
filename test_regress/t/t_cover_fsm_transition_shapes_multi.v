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
  state_t state_q  /*verilator fsm_state*/;
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

module fsm_normalized_if_noelse (
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
  state_t state_q  /*verilator fsm_state*/;
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

module fsm_forced_wide (
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

module fsm_forced_if_wide (
    input logic clk
);

  // Forced non-enum FSMs infer only values observed in the transition logic
  logic [30:0] state  /*verilator fsm_state*/;

  always_ff @(posedge clk) begin
    if (state == 31'd0) state <= 31'd1;
    else if (state == 31'd1) state <= 31'd0;
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

module fsm_oneblock_guarded (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic rst;
  integer cyc;
  state_t state_q;

  initial begin
    rst = 1'b1;
    cyc = 0;
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
  end
  // A register that is not assigned holds its state
  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else
      case (state_q)
        S0: if (cyc[0]) state_q <= S1;
        S1:
        if (cyc[1]) state_q <= S2;
        else if (cyc[2]) state_q <= S0;
        default: state_q <= S0;
      endcase
  end
endmodule

module fsm_forced_guarded (
    input logic clk
);
  localparam logic [1:0] IDLE = 2'd0;
  localparam logic [1:0] RUN = 2'd1;
  localparam logic [1:0] DONE = 2'd2;
  logic rst;
  integer cyc;
  logic [1:0] state_q  /*verilator fsm_state*/;
  logic [1:0] state_d;

  initial begin
    rst = 1'b1;
    cyc = 0;
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
  end
  // DONE is only a guarded target, not a case item
  always_comb begin
    state_d = state_q;
    case (state_q)
      IDLE: if (cyc[0]) state_d = RUN;
      RUN: if (!cyc[0]) state_d = DONE;
      default: ;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) state_q <= IDLE;
    else state_q <= state_d;
  end
endmodule

module fsm_enable (
    input logic clk,
    input logic rst,
    input logic en
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic rst_n;
  assign rst_n = !rst;
  logic sel;
  assign sel = en;

  // Registers with an enable, which otherwise holds the state

  state_t elsif_q;
  state_t elsif_d;
  always_comb begin
    elsif_d = elsif_q;
    case (elsif_q)
      S0: elsif_d = S1;
      S1: elsif_d = S2;
      S2: elsif_d = S0;
      default: elsif_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) elsif_q <= S0;
    else if (en) elsif_q <= elsif_d;
  end

  state_t cond_q;
  state_t cond_d;
  always_comb begin
    cond_d = cond_q;
    case (cond_q)
      S0: cond_d = S1;
      S1: cond_d = S2;
      S2: cond_d = S0;
      default: cond_d = S0;
    endcase
  end
  always_ff @(posedge clk) cond_q <= rst ? S0 : (en ? cond_d : cond_q);

  state_t lowrst_q;
  state_t lowrst_d;
  always_comb begin
    lowrst_d = lowrst_q;
    case (lowrst_q)
      S0: lowrst_d = S1;
      S1: lowrst_d = S2;
      S2: lowrst_d = S0;
      default: lowrst_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (!rst_n) lowrst_q <= S0;
    else if (en) lowrst_q <= lowrst_d;
  end

  state_t noreset_q;
  state_t noreset_d;
  always_comb begin
    noreset_d = noreset_q;
    case (noreset_q)
      S0: noreset_d = S1;
      S1: noreset_d = S2;
      S2: noreset_d = S0;
      default: noreset_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (en) noreset_q <= noreset_d;
  end

  state_t noreset_cond_q;
  state_t noreset_cond_d;
  always_comb begin
    noreset_cond_d = noreset_cond_q;
    case (noreset_cond_q)
      S0: noreset_cond_d = S1;
      S1: noreset_cond_d = S2;
      S2: noreset_cond_d = S0;
      default: noreset_cond_d = S0;
    endcase
  end
  always_ff @(posedge clk) noreset_cond_q <= en ? noreset_cond_d : noreset_cond_q;

  state_t lowcond_q;
  state_t lowcond_d;
  always_comb begin
    lowcond_d = lowcond_q;
    case (lowcond_q)
      S0: lowcond_d = S1;
      S1: lowcond_d = S2;
      S2: lowcond_d = S0;
      default: lowcond_d = S0;
    endcase
  end
  always_ff @(posedge clk) lowcond_q <= rst_n ? (en ? lowcond_d : lowcond_q) : S0;

  state_t hold_q;
  state_t hold_d;
  always_comb begin
    hold_d = hold_q;
    case (hold_q)
      S0: hold_d = S1;
      S1: hold_d = S2;
      S2: hold_d = S0;
      default: hold_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) hold_q <= S0;
    else if (en) hold_q <= hold_d;
    else hold_q <= hold_q;
  end

  state_t noreset_hold_q;
  state_t noreset_hold_d;
  always_comb begin
    noreset_hold_d = noreset_hold_q;
    case (noreset_hold_q)
      S0: noreset_hold_d = S1;
      S1: noreset_hold_d = S2;
      S2: noreset_hold_d = S0;
      default: noreset_hold_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (en) noreset_hold_q <= noreset_hold_d;
    else noreset_hold_q <= noreset_hold_q;
  end

  state_t nest_cond_q;
  state_t nest_cond_d;
  always_comb begin
    nest_cond_d = nest_cond_q;
    case (nest_cond_q)
      S0: nest_cond_d = S1;
      S1: nest_cond_d = S2;
      S2: nest_cond_d = S0;
      default: nest_cond_d = S0;
    endcase
  end
  always_ff @(posedge clk) nest_cond_q <= rst ? S0 : (en ? (sel ? nest_cond_d : nest_cond_q) : nest_cond_q);

  state_t nest_if_q;
  state_t nest_if_d;
  always_comb begin
    nest_if_d = nest_if_q;
    case (nest_if_q)
      S0: nest_if_d = S1;
      S1: nest_if_d = S2;
      S2: nest_if_d = S0;
      default: nest_if_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) nest_if_q <= S0;
    else if (en) begin
      if (sel) nest_if_q <= nest_if_d;
    end
  end

  // An enable that holds the state when set
  logic stall;
  assign stall = !en;

  state_t stall_q;
  state_t stall_d;
  always_comb begin
    stall_d = stall_q;
    case (stall_q)
      S0: stall_d = S1;
      S1: stall_d = S2;
      S2: stall_d = S0;
      default: stall_d = S0;
    endcase
  end
  always_ff @(posedge clk) stall_q <= rst ? S0 : (stall ? stall_q : stall_d);

  // Not enables, so no FSM: neither arm holds the state, an arm is not a single value, or
  // the else holds another register
  state_t sel_q;
  state_t a_d;
  state_t b_d;
  assign a_d = S1;
  assign b_d = S2;
  always_ff @(posedge clk) sel_q <= rst ? S0 : (sel ? a_d : b_d);
  state_t nest_q;
  always_ff @(posedge clk) nest_q <= rst ? S0 : (en ? (sel ? a_d : b_d) : nest_q);
  state_t then_q;
  always_ff @(posedge clk) then_q <= rst ? (sel ? a_d : b_d) : then_q;
  state_t badhold_q;
  always_ff @(posedge clk) begin
    if (en) badhold_q <= a_d;
    else badhold_q <= then_q;
  end
  state_t else_q;
  always_ff @(posedge clk) else_q <= rst ? S0 : (en ? else_q : (sel ? a_d : b_d));
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
  fsm_normalized_if_noelse normalized_if_noelse_u (.clk(clk));
  fsm_normalized_if_then_nonconst_bad normalized_if_then_nonconst_bad_u (.clk(clk));
  fsm_normalized_if_else_nonconst_bad normalized_if_else_nonconst_bad_u (.clk(clk));
  fsm_normalized_if_temp_mismatch_bad normalized_if_temp_mismatch_bad_u (.clk(clk));
  fsm_normalized_if_then_state_else_other_bad normalized_if_then_state_else_other_bad_u (.clk(clk));
  fsm_normalized_if_same_temp_nofollow_bad normalized_if_same_temp_nofollow_bad_u (.clk(clk));
  fsm_normalized_if_follow_nonvar_bad normalized_if_follow_nonvar_bad_u (.clk(clk));
  fsm_normalized_if_follow_wrongfrom_bad normalized_if_follow_wrongfrom_bad_u (.clk(clk));
  fsm_normalized_if_follow_wronglhs_bad normalized_if_follow_wronglhs_bad_u (.clk(clk));
  fsm_case_next_wrongrhs_bad case_next_wrongrhs_bad_u (.clk(clk));
  fsm_forced_wide forced_wide_u (.clk(clk));
  fsm_enable enable_u (
      .clk(clk),
      .rst(cyc == 0),
      .en(cyc[0])
  );
  fsm_forced_if_wide forced_if_wide_u (.clk(clk));
  fsm_reset_commit_mismatch_bad reset_commit_mismatch_bad_u (.clk(clk));
  fsm_reset_then_bad reset_then_bad_u (.clk(clk));
  fsm_oneblock_guarded oneblock_guarded_u (.clk(clk));
  fsm_forced_guarded forced_guarded_u (.clk(clk));

  initial cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
