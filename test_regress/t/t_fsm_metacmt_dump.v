// DESCRIPTION: Verilator: FSM metacomment dump test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic rst
);

  typedef enum logic [0:0] {
    S0 = 1'b0,
    S1 = 1'b1
  } state_t;

  state_t state_reset /*verilator fsm_reset_arc*/;
  state_t state_cond /*verilator fsm_arc_include_cond*/;
  logic forced_state /*verilator fsm_state*/;

  always_ff @(posedge clk) begin
    if (rst) begin
      state_reset <= S0;
      state_cond <= S0;
      forced_state <= 1'b0;
    end else begin
      state_reset <= S1;
      if (state_cond) state_cond <= S0;
      else state_cond <= S1;
      forced_state <= ~forced_state;
    end
  end

endmodule
