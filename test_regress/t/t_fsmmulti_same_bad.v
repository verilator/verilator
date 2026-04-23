// DESCRIPTION: Verilator: same-state multi-candidate FSM error test
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
    S1,
    S2
  } state_t;

  state_t state;

  // This is intentionally non-idiomatic RTL. The detector sees one supported
  // candidate in the reset-if else branch and a second supported top-level
  // case on the same state variable. That same-state duplicate is rejected.
  always_ff @(posedge clk) begin
    if (rst) begin
      state <= S0;
    end
    else begin
      case (state)
        S0: state <= S1;
        default: ;
      endcase
    end
    case (state)
      S1: state <= S2;
      default: ;
    endcase
  end

endmodule
