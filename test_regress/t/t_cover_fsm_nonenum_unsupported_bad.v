// DESCRIPTION: Verilator: FSM coverage warns on unsupported non-enum state spaces
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
  localparam logic [1:0] RESET = 2'h0;
  localparam logic [1:0] BUSY = 2'h1;
  localparam logic [1:0] _IDLE = 2'h0;

  logic [32:0] wide_state;
  logic [1:0] target_state;
  logic [1:0] duplicate_state;
  logic [1:0] duplicate_ternary_target_state;
  logic [1:0] duplicate_ternary_then_target_state;
  logic [1:0] duplicate_if_target_state;
  logic [1:0] duplicate_if_ternary_then_target_state;
  logic [1:0] duplicate_if_ternary_else_target_state;
  logic [1:0] xz_case_state;
  logic [1:0] duplicate_literal_state;
  logic [1:0] underscore_state;
  logic [1:0] xz_reset_probe_state;
  logic [1:0] xz_rhs_probe_state  /*verilator fsm_state*/;
  logic [1:0] nonconst_ternary_target_state  /*verilator fsm_state*/;
  logic [32:0] wide_if_state  /*verilator fsm_state*/;

  always_ff @(posedge clk) begin
    if (rst) begin
      wide_state <= 33'h0;
    end
    else begin
      case (wide_state)
        33'h0: wide_state <= 33'h1;
        33'h1: wide_state <= 33'h0;
        default: wide_state <= 33'h0;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      target_state <= 2'h0;
    end
    else begin
      case (target_state)
        2'h0: target_state <= 2'h1;
        2'h1: target_state <= 2'h2;
        default: target_state <= 2'h0;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      duplicate_state <= IDLE;
    end
    else begin
      /* verilator lint_off CASEOVERLAP */
      case (duplicate_state)
        IDLE: duplicate_state <= start ? BUSY : IDLE;
        RESET: duplicate_state <= IDLE;
        BUSY: duplicate_state <= IDLE;
        default: duplicate_state <= IDLE;
      endcase
      /* verilator lint_on CASEOVERLAP */
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      xz_case_state <= 2'h0;
    end
    else begin
      /* verilator lint_off CASEWITHX */
      case (xz_case_state)
        2'h0: xz_case_state <= 2'h1;
        2'b1x: xz_case_state <= 2'h0;
        default: xz_case_state <= 2'h0;
      endcase
      /* verilator lint_on CASEWITHX */
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      duplicate_ternary_target_state <= IDLE;
    end
    else begin
      case (duplicate_ternary_target_state)
        IDLE: duplicate_ternary_target_state <= start ? BUSY : RESET;
        BUSY: duplicate_ternary_target_state <= IDLE;
        default: duplicate_ternary_target_state <= IDLE;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      duplicate_ternary_then_target_state <= IDLE;
    end
    else begin
      case (duplicate_ternary_then_target_state)
        IDLE: duplicate_ternary_then_target_state <= start ? RESET : BUSY;
        BUSY: duplicate_ternary_then_target_state <= IDLE;
        default: duplicate_ternary_then_target_state <= IDLE;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      duplicate_if_target_state <= IDLE;
    end
    else if (duplicate_if_target_state == IDLE) begin
      duplicate_if_target_state <= BUSY;
    end
    else if (duplicate_if_target_state == BUSY) begin
      duplicate_if_target_state <= RESET;
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      duplicate_if_ternary_then_target_state <= IDLE;
    end
    else if (duplicate_if_ternary_then_target_state == IDLE) begin
      duplicate_if_ternary_then_target_state <= start ? RESET : BUSY;
    end
    else if (duplicate_if_ternary_then_target_state == BUSY) begin
      duplicate_if_ternary_then_target_state <= IDLE;
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      duplicate_if_ternary_else_target_state <= IDLE;
    end
    else if (duplicate_if_ternary_else_target_state == IDLE) begin
      duplicate_if_ternary_else_target_state <= start ? BUSY : RESET;
    end
    else if (duplicate_if_ternary_else_target_state == BUSY) begin
      duplicate_if_ternary_else_target_state <= IDLE;
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      duplicate_literal_state <= 2'h0;
    end
    else begin
      /* verilator lint_off CASEOVERLAP */
      case (duplicate_literal_state)
        2'h0: duplicate_literal_state <= start ? 2'h1 : 2'h0;
        2'h0: duplicate_literal_state <= 2'h0;
        2'h1: duplicate_literal_state <= 2'h0;
        default: duplicate_literal_state <= 2'h0;
      endcase
      /* verilator lint_on CASEOVERLAP */
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      underscore_state <= _IDLE;
    end
    else begin
      case (underscore_state)
        _IDLE: underscore_state <= BUSY;
        BUSY: underscore_state <= _IDLE;
        default: underscore_state <= _IDLE;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      xz_reset_probe_state <= 2'b0x;
    end
    else begin
      case (xz_reset_probe_state)
        2'h0: xz_reset_probe_state <= 2'h1;
        2'h1: xz_reset_probe_state <= 2'h0;
        default: xz_reset_probe_state <= 2'h0;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      xz_rhs_probe_state <= 2'h0;
    end
    else begin
      case (xz_rhs_probe_state)
        2'h0: xz_rhs_probe_state <= 2'b0x;
        2'h1: xz_rhs_probe_state <= 2'h0;
        default: xz_rhs_probe_state <= 2'h0;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      nonconst_ternary_target_state <= 2'h0;
    end
    else begin
      case (nonconst_ternary_target_state)
        2'h0: nonconst_ternary_target_state <= start ? 2'h1 : {1'b0, start};
        2'h1: nonconst_ternary_target_state <= 2'h0;
        default: nonconst_ternary_target_state <= 2'h0;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      wide_if_state <= 33'h0;
    end
    else if (wide_if_state == 33'h0) begin
      wide_if_state <= 33'h1;
    end
    else if (wide_if_state == 33'h1) begin
      wide_if_state <= 33'h0;
    end
  end

  logic [1:0] not_const_item_state;

  always_ff @(posedge clk) begin
    if (rst) begin
      not_const_item_state <= 2'h0;
    end
    else begin
      case (not_const_item_state)
        2'h0: not_const_item_state <= 2'h1;
        {1'b0, start}: not_const_item_state <= 2'h0;
        2'h1: not_const_item_state <= 2'h0;
        default: not_const_item_state <= 2'h0;
      endcase
    end
  end

endmodule
