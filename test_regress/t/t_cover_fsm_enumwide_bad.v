// DESCRIPTION: Verilator: FSM enum width limit rejects >32-bit enums
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic rst
);

  typedef enum logic [32:0] {
    S0 = 33'd0,
    S1 = 33'd1
  } state_t;

  state_t state;

  // FSM coverage currently supports enum-backed state variables only up to
  // 32 bits wide, so this wider enum should be rejected at FSM detection time.
  always_ff @(posedge clk) begin
    if (rst) begin
      state <= S0;
    end
    else begin
      case (state)
        S0: state <= S1;
        default: state <= S0;
      endcase
    end
  end

endmodule
