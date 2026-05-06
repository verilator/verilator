// DESCRIPTION: Verilator: FSM rejects unknown enum constants in direct and conditional transitions
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Group the same unsupported warning family across direct, conditional, and
// reset-driven enum assignments that use constants outside the declared enum.

module unknown_then (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  logic sel;
  state_t state_q  /*verilator fsm_state*/;
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
  state_t state_q  /*verilator fsm_state*/;
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

module unknown_direct (
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
    case (state_q)
      /* verilator lint_off ENUMVALUE */
      S0: state_d = 2'd3;
      /* verilator lint_on ENUMVALUE */
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module unknown_reset (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  logic rst;
  integer cyc;
  state_t state_q  /*verilator fsm_reset_arc*/;
  state_t state_d;

  initial begin
    rst = 1'b1;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
  end

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = S1;
      default: state_d = S0;
    endcase
  end

  // Reset-arc extraction uses a separate path from steady-state case-item arc
  // extraction, so keep one reset-only bad enum target in this grouped test.
  always_ff @(posedge clk) begin
    if (rst) begin
      /* verilator lint_off ENUMVALUE */
      state_q <= 2'd3;
      /* verilator lint_on ENUMVALUE */
    end
    else begin
      state_q <= state_d;
    end
  end
endmodule

module t;
  logic clk;
  unknown_then unknown_then_u (.clk(clk));
  unknown_else unknown_else_u (.clk(clk));
  unknown_direct unknown_direct_u (.clk(clk));
  unknown_reset unknown_reset_u (.clk(clk));
endmodule
