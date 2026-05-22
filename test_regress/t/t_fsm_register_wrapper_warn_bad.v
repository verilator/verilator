// DESCRIPTION: Verilator: FSM register wrapper VLT warning coverage
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

module missing_q_fsm_flop #(
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

module missing_clock_fsm_flop #(
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

module partial_reset_fsm_flop #(
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

module missing_reset_value_fsm_flop #(
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

module value_no_reset_fsm_flop #(
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

module sync_reset_fsm_flop #(
    parameter int Width = 1,
    parameter logic [Width-1:0] ResetValue = '0
) (
    input logic clk,
    input logic rst,
    input logic [Width-1:0] din,
    output logic [Width-1:0] dout
);
  always_ff @(posedge clk) begin
    if (rst) dout <= ResetValue;
    else dout <= din;
  end
endmodule

module missing_reset_connection_fsm_flop #(
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

module t (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  logic rst_n;
  logic rst;
  state_t state_q;
  state_t missing_d;
  state_t missing_q;
  state_t missing_clock_d;
  state_t missing_clock_q;
  state_t partial_reset_d;
  state_t partial_reset_q;
  state_t missing_reset_value_d;
  state_t missing_reset_value_q;
  state_t value_no_reset_d;
  state_t value_no_reset_q;
  state_t sync_reset_d;
  state_t sync_reset_q;
  state_t missing_reset_connection_d;
  state_t missing_reset_connection_q;

  odd_fsm_flop #(
      .Width($bits(state_t)),
      .ResetValue(S0)
  ) u_bad_simple (
      .clk(clk),
      .rst_n(rst_n),
      .din(S0),
      .dout(state_q)
  );

  missing_q_fsm_flop #(
      .Width($bits(state_t)),
      .ResetValue(S0)
  ) u_missing_q_port (
      .clk(clk),
      .rst_n(rst_n),
      .din(missing_d),
      .dout(missing_q)
  );

  missing_clock_fsm_flop #(
      .Width($bits(state_t)),
      .ResetValue(S0)
  ) u_missing_clock_port (
      .clk(clk),
      .rst_n(rst_n),
      .din(missing_clock_d),
      .dout(missing_clock_q)
  );

  partial_reset_fsm_flop #(
      .Width($bits(state_t)),
      .ResetValue(S0)
  ) u_partial_reset (
      .clk(clk),
      .rst_n(rst_n),
      .din(partial_reset_d),
      .dout(partial_reset_q)
  );

  missing_reset_value_fsm_flop #(
      .Width($bits(state_t)),
      .ResetValue(S0)
  ) u_missing_reset_value (
      .clk(clk),
      .rst_n(rst_n),
      .din(missing_reset_value_d),
      .dout(missing_reset_value_q)
  );

  value_no_reset_fsm_flop #(
      .Width($bits(state_t)),
      .ResetValue(S0)
  ) u_value_no_reset (
      .clk(clk),
      .rst_n(rst_n),
      .din(value_no_reset_d),
      .dout(value_no_reset_q)
  );

  sync_reset_fsm_flop #(
      .Width($bits(state_t)),
      .ResetValue(S0)
  ) u_sync_reset (
      .clk(clk),
      .rst(rst),
      .din(sync_reset_d),
      .dout(sync_reset_q)
  );

  missing_reset_connection_fsm_flop #(
      .Width($bits(state_t)),
      .ResetValue(S0)
  ) u_missing_reset_connection (
      .clk(clk),
      .rst_n(rst_n),
      .din(missing_reset_connection_d),
      .dout(missing_reset_connection_q)
  );
endmodule
