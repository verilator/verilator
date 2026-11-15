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

  // An enable whose then or else arm writes the state in a concatenation
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic en;
  assign en = cyc[0];
  state_t both_q;
  state_t both_d;
  logic both_x;
  always_comb begin
    both_d = both_q;
    case (both_q)
      S0: both_d = S1;
      S1: both_d = S2;
      default: both_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) both_q <= S0;
    else if (en) {both_x, both_q} <= {1'b0, both_d};
    else {both_x, both_q} <= {both_x, both_q};
  end
  state_t else_q;
  state_t else_d;
  logic else_x;
  always_comb begin
    else_d = else_q;
    case (else_q)
      S0: else_d = S1;
      S1: else_d = S2;
      default: else_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) else_q <= S0;
    else if (en) else_q <= else_d;
    else {else_x, else_q} <= {else_x, else_q};
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
