// DESCRIPTION: Verilator: FSM coverage obfuscated empty reset branch internal error
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic rst,
    input logic input_valid,
    input logic input_last,
    input logic output_ready,
    input logic [6:0] input_data,
    output logic [6:0] output_data,
    output logic output_valid
);
  typedef enum logic [1:0] {
    WAITING,
    COLLECTING,
    SENDING
  } state_t;

  state_t state;
  logic [6:0] saved_data;

  always_ff @(posedge clk) begin
    if (rst) begin
    end
    else if (state == WAITING) begin
      if (input_valid) begin
        saved_data <= input_data;
        state <= input_last ? SENDING : COLLECTING;
      end
      else begin
        state <= WAITING;
      end
    end
    else if (state == COLLECTING) begin
      if (input_valid && input_last) begin
        state <= SENDING;
      end
      else begin
        state <= COLLECTING;
      end
    end
    else if (state == SENDING) begin
      if (output_ready) begin
        state <= WAITING;
      end
      else begin
        state <= SENDING;
      end
    end
  end

  always_comb begin
    output_valid = state == SENDING;
    output_data = saved_data;
  end
endmodule
