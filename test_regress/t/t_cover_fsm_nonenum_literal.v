// DESCRIPTION: Verilator: FSM coverage infers non-enum state space
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic rst,
    input logic start
);

  localparam logic [1:0] IDLE = 2'h0;
  localparam logic [1:0] BUSY = 2'h1;
  localparam logic [1:0] DONE = 2'h2;
  localparam logic [1:0] BODY_ID = 2'h0;
  localparam logic [1:0] BODY$ID = 2'h1;

  logic [1:0] literal_state;
  logic [1:0] param_state;
  logic unbased_state;
  logic [1:0] body_symbol_state;
  logic [1:0] multiline_expr_state;
  logic [1:0] duplicate_expr_state;
  logic [1:0] duplicate_same_label_state;
  logic [1:0] duplicate_expr_first_state;

  always_ff @(posedge clk) begin
    if (rst) begin
      literal_state <= 2'h0;
    end
    else begin
      case (literal_state)
        2'h0: literal_state <= start ? 2'h1 : 2'h0;
        2'h1: literal_state <= 2'h2;
        2'h2: literal_state <= 2'h2;
        default: literal_state <= 2'h0;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      param_state <= IDLE;
    end
    else begin
      case (param_state)
        IDLE: param_state <= start ? BUSY : IDLE;
        BUSY: param_state <= DONE;
        DONE: param_state <= DONE;
        default: param_state <= IDLE;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      unbased_state <= '0;
    end
    else begin
      case (unbased_state)
        '0: unbased_state <= '1;
        '1: unbased_state <= '0;
        default: unbased_state <= '0;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      body_symbol_state <= BODY_ID;
    end
    else begin
      case (body_symbol_state)
        BODY_ID
            : body_symbol_state <= BODY$ID;
        BODY$ID: body_symbol_state <= BODY_ID;
        default: body_symbol_state <= BODY_ID;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      multiline_expr_state <= 2'h0;
    end
    else begin
      case (multiline_expr_state)
        (2'h0
         + 2'h0): multiline_expr_state <= 2'h1;
        2'h1: multiline_expr_state <= 2'h0;
        default: multiline_expr_state <= 2'h0;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      duplicate_expr_state <= IDLE;
    end
    else begin
      /* verilator lint_off CASEOVERLAP */
      case (duplicate_expr_state)
        IDLE: duplicate_expr_state <= BUSY;
        (2'h0
         + 2'h0): duplicate_expr_state <= BUSY;
        BUSY: duplicate_expr_state <= IDLE;
        default: duplicate_expr_state <= IDLE;
      endcase
      /* verilator lint_on CASEOVERLAP */
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      duplicate_same_label_state <= IDLE;
    end
    else begin
      /* verilator lint_off CASEOVERLAP */
      case (duplicate_same_label_state)
        IDLE: duplicate_same_label_state <= BUSY;
        IDLE: duplicate_same_label_state <= BUSY;
        BUSY: duplicate_same_label_state <= IDLE;
        default: duplicate_same_label_state <= IDLE;
      endcase
      /* verilator lint_on CASEOVERLAP */
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      duplicate_expr_first_state <= 2'h0;
    end
    else begin
      /* verilator lint_off CASEOVERLAP */
      case (duplicate_expr_first_state)
        (2'h0
         + 2'h0): duplicate_expr_first_state <= BUSY;
        IDLE: duplicate_expr_first_state <= BUSY;
        BUSY: duplicate_expr_first_state <= 2'h0;
        default: duplicate_expr_first_state <= 2'h0;
      endcase
      /* verilator lint_on CASEOVERLAP */
    end
  end

endmodule
