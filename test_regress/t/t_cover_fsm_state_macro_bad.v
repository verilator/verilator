// DESCRIPTION: Verilator: FSM macro wrapper warning coverage
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module odd_fsm_flop #(
    parameter int Width = 1,
    parameter logic [Width-1:0] ResetValue = '0
) (
    input logic clk,
    input logic rst_n,
    input logic [Width-1:0] din,
    output logic [Width-1:0] dout
);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) dout <= ResetValue;
    else dout <= din;
  end
endmodule

module odd_clock_fsm_flop #(
    parameter int Width = 1,
    parameter logic [Width-1:0] ResetValue = '0
) (
    input logic clock,
    input logic rst_n,
    input logic [Width-1:0] din,
    output logic [Width-1:0] dout
);
  always_ff @(posedge clock or negedge rst_n) begin
    if (!rst_n) dout <= ResetValue;
    else dout <= din;
  end
endmodule

module t (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  logic rst_n;
  state_t state_q;
  state_t state_d;
  state_t bad_q;
  state_t bad_d;
  state_t missing_q;
  state_t missing_d;
  state_t malformed_q;
  state_t malformed_d;
  state_t unknown_q;
  state_t unknown_d;
  state_t no_clock_q;
  state_t no_clock_d;
  state_t missing_port_q;
  state_t missing_port_d;
  state_t missing_q_port_q;
  state_t missing_q_port_d;

  always_comb begin
    state_d = state_q;
    if (state_q == S0) state_d = S1;
  end

  odd_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_bad_simple (
    .clk(clk),
    .rst_n(rst_n),
    .din(S0),
    .dout(state_q)
  ) /*verilator fsm_state_macro d=din q=dout clk=clk rst=rst_n rstval=ResetValue*/;

  odd_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_missing_roles (
    .clk(clk),
    .rst_n(rst_n),
    .din(missing_d),
    .dout(missing_q)
  ) /*verilator fsm_state_macro*/;

  odd_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_malformed (
    .clk(clk),
    .rst_n(rst_n),
    .din(malformed_d),
    .dout(malformed_q)
  ) /*verilator fsm_state_macro !bad q = dout stray d=*/;

  odd_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_unknown (
    .clk(clk),
    .rst_n(rst_n),
    .din(unknown_d),
    .dout(unknown_q)
  ) /*verilator fsm_state_macro d = din  q = dout   dee = din   */;

  odd_clock_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_no_clock (
    .clock(clk),
    .rst_n(rst_n),
    .din(no_clock_d),
    .dout(no_clock_q)
  ) /*verilator fsm_state_macro d=din q=dout rst=rst_n rstval=ResetValue*/;

  odd_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_missing_port (
    .clk(clk),
    .rst_n(rst_n),
    .din(missing_port_d),
    .dout(missing_port_q)
  ) /*verilator fsm_state_macro d=missing q=dout clk=clk rst=rst_n rstval=ResetValue*/;

  odd_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_missing_q_port (
    .clk(clk),
    .rst_n(rst_n),
    .din(missing_q_port_d),
    .dout(missing_q_port_q)
  ) /*verilator fsm_state_macro d=din q=missing clk=clk rst=rst_n rstval=ResetValue*/;
endmodule
