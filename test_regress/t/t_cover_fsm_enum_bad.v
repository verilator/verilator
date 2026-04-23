// DESCRIPTION: Verilator: FSM enum transition rejects unknown constant values
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic rst
);

  typedef enum logic [1:0] {
    S0,
    S1
  } state_t;

  state_t state;

  // FSM coverage should reject a constant next-state value that is not one of
  // the declared enum items. This keeps graph construction aligned with the
  // enum-backed state set instead of silently dropping the transition.
  always_ff @(posedge clk) begin
    if (rst) begin
      state <= S0;
    end
    else begin
      case (state)
        /* verilator lint_off ENUMVALUE */
        S0: state <= 2'd3;
        /* verilator lint_on ENUMVALUE */
        default: state <= S0;
      endcase
    end
  end

endmodule
