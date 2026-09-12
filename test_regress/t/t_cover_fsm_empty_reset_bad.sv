// DESCRIPTION: Verilator: FSM coverage empty reset branch internal error
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic rst,
    input logic go
);
  typedef enum logic {
    IDLE,
    BUSY
  } state_t;

  state_t state;
  state_t state_next;

  always_ff @(posedge clk) begin
    if (rst) begin
    end
    else state <= state_next;
  end

  always_comb begin
    state_next = state;
    case (state)
      IDLE: state_next = go ? BUSY : IDLE;
      default: state_next = IDLE;
    endcase
  end
endmodule
