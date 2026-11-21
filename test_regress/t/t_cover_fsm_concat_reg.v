// DESCRIPTION: Verilator: FSM coverage ignores a register written as a concatenation
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 David Harris
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  logic [1:0] hi;
  logic [1:0] lo;
  logic [3:0] next;
  logic rst;
  int cyc;

  assign next = {hi, lo} + 4'd1;

  always_ff @(posedge clk) {hi, lo} <= rst ? 4'd0 : next;

  // Registers assigned through a concatenation, in a case item's arm and in the reset branch
  // of an if chain, a case and an active-low case: none is reported as an FSM
  localparam logic [1:0] S0 = 2'd0;
  localparam logic [1:0] S1 = 2'd1;
  localparam logic [1:0] S2 = 2'd2;
  logic [1:0] state_q, state_d;
  logic done;
  always_comb begin
    state_d = state_q;
    done = 1'b0;
    case (state_q)
      S0: state_d = S1;
      S1:
      if (cyc[0]) {done, state_d} = {1'b1, S2};
      else state_d = S0;
      default: state_d = S0;
    endcase
  end
  always_ff @(posedge clk) state_q <= state_d;

  logic [1:0] state2;
  logic flag2;
  always_ff @(posedge clk) begin
    if (rst) {flag2, state2} <= '0;
    else if (state2 == S0) state2 <= S1;
    else state2 <= S0;
  end

  logic [1:0] state3;
  logic flag3;
  always_ff @(posedge clk) begin
    if (rst) {flag3, state3} <= '0;
    else
      case (state3)
        S0: state3 <= S1;
        default: state3 <= S0;
      endcase
  end

  logic [1:0] state4;
  logic flag4;
  logic rst_n;
  assign rst_n = !rst;
  always_ff @(posedge clk) begin
    if (rst_n)
      case (state4)
        S0: state4 <= S1;
        default: state4 <= S0;
      endcase
    else {flag4, state4} <= '0;
  end

  initial cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    rst <= (cyc == 0);
    if (cyc == 5) begin
      if ({hi, lo} != 4'd3) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
