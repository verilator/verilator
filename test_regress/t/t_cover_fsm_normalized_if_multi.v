// DESCRIPTION: Verilator: FSM coverage ignores grouped normalized-if and case(state_d) reject shapes
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module if_noelse_case (
    input logic clk
);
  typedef enum logic [1:0] { S0 = 2'd0, S1 = 2'd1, S2 = 2'd2 } state_t;
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
    case (state_q)
      S0: if (start) ; else state_d = S1;
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module if_then_nonconst_case (
    input logic clk
);
  typedef enum logic [1:0] { S0 = 2'd0, S1 = 2'd1, S2 = 2'd2 } state_t;
  logic sel;
  integer cyc;
  state_t state_q /*verilator fsm_state*/;
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

module if_else_nonconst_case (
    input logic clk
);
  typedef enum logic [1:0] { S0 = 2'd0, S1 = 2'd1, S2 = 2'd2 } state_t;
  logic sel;
  integer cyc;
  state_t state_q /*verilator fsm_state*/;
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

module if_temp_mismatch_case (
    input logic clk
);
  typedef enum logic [1:0] { S0 = 2'd0, S1 = 2'd1, S2 = 2'd2 } state_t;
  logic sel;
  integer cyc;
  state_t state_q /*verilator fsm_state*/;
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

module if_then_state_else_other_case (
    input logic clk
);
  typedef enum logic [1:0] { S0 = 2'd0, S1 = 2'd1, S2 = 2'd2 } state_t;
  logic sel;
  integer cyc;
  state_t state_q /*verilator fsm_state*/;
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

module if_same_temp_nofollow_case (
    input logic clk
);
  typedef enum logic [1:0] { S0 = 2'd0, S1 = 2'd1, S2 = 2'd2 } state_t;
  logic sel;
  logic aux;
  integer cyc;
  state_t state_q /*verilator fsm_state*/;
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
        end else begin
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

module if_follow_nonvar_case (
    input logic clk
);
  typedef enum logic [1:0] { S0 = 2'd0, S1 = 2'd1, S2 = 2'd2 } state_t;
  logic sel;
  logic aux;
  integer cyc;
  state_t state_q /*verilator fsm_state*/;
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
        end else begin
          tmp_a = S2;
          aux = 1'b0;
        end
        state_d = S1;
      end
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module if_follow_wrongfrom_case (
    input logic clk
);
  typedef enum logic [1:0] { S0 = 2'd0, S1 = 2'd1, S2 = 2'd2 } state_t;
  logic sel;
  logic aux;
  integer cyc;
  state_t state_q /*verilator fsm_state*/;
  state_t state_d;
  state_t tmp_a;
  state_t tmp_b;

  initial begin
    sel = 1'b0;
    cyc = 0;
    tmp_b = S2;
  end
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
  end
  always_comb begin
    aux = 1'b0;
    state_d = state_q;
    case (state_q)
      S0: begin
        if (sel) begin
          tmp_a = S1;
          aux = 1'b1;
        end else begin
          tmp_a = S2;
          aux = 1'b0;
        end
        state_d = tmp_b;
      end
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module if_follow_wronglhs_case (
    input logic clk
);
  typedef enum logic [1:0] { S0 = 2'd0, S1 = 2'd1, S2 = 2'd2 } state_t;
  logic sel;
  logic aux;
  integer cyc;
  state_t state_q /*verilator fsm_state*/;
  state_t state_d;
  state_t other_d;
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
    aux = 1'b0;
    state_d = state_q;
    case (state_q)
      S0: begin
        if (sel) begin
          tmp_a = S1;
          aux = 1'b1;
        end else begin
          tmp_a = S2;
          aux = 1'b0;
        end
        other_d = tmp_a;
      end
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module case_next_wrongrhs_case (
    input logic clk
);
  typedef enum logic [1:0] { S0 = 2'd0, S1 = 2'd1, S2 = 2'd2 } state_t;
  logic rst;
  logic start;
  integer cyc;
  state_t state_q /*verilator fsm_reset_arc*/;
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

module t (
    input logic clk
);
  integer cyc;

  if_noelse_case if_noelse_case_u(.clk(clk));
  if_then_nonconst_case if_then_nonconst_case_u(.clk(clk));
  if_else_nonconst_case if_else_nonconst_case_u(.clk(clk));
  if_temp_mismatch_case if_temp_mismatch_case_u(.clk(clk));
  if_then_state_else_other_case if_then_state_else_other_case_u(.clk(clk));
  if_same_temp_nofollow_case if_same_temp_nofollow_case_u(.clk(clk));
  if_follow_nonvar_case if_follow_nonvar_case_u(.clk(clk));
  if_follow_wrongfrom_case if_follow_wrongfrom_case_u(.clk(clk));
  if_follow_wronglhs_case if_follow_wronglhs_case_u(.clk(clk));
  case_next_wrongrhs_case case_next_wrongrhs_case_u(.clk(clk));

  initial begin
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
