// DESCRIPTION: Verilator: FSM coverage ignores non-matching plain always scan shapes
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Group plain-always warning-scan shapes that should be ignored silently
// before the detector ever decides an FSM candidate is present.

module ignore_sel_expr (
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

  // Plain always with a non-VarRef selector should be ignored silently.
  always @(posedge clk) begin
    state_d = state_q;
    case (state_q + 1)
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

module ignore_other_selector (
    input logic clk,
    input logic rst,
    input logic start,
    input logic other
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_reset_arc*/;
  state_t state_d;

  // Plain always with an unrelated selector should also be ignored silently.
  always @(posedge clk) begin
    state_d = state_q;
    case (other)
      1'b0: state_d = start ? S1 : S0;
      default: state_d = S2;
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
  logic rst;
  logic start;
  logic other;
  integer cyc;

  ignore_sel_expr ignore_sel_expr_u (.*);
  ignore_other_selector ignore_other_selector_u (.*);

  initial begin
    rst = 1'b1;
    start = 1'b0;
    other = 1'b0;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) start <= 1'b0;
    if (cyc == 4) other <= 1'b1;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
