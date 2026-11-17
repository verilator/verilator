// DESCRIPTION: Verilator: FSM coverage warns of enum registers given values outside the enum
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic rst,
    input logic go,
    input logic drop
);
  typedef enum logic [1:0] {
    E0 = 2'd0,
    E1 = 2'd1,
    E2 = 2'd2
  } e_t;
  // The reset value, the transition under 'drop' from every state, and the E1 transition
  // are outside the enum: each is warned once
  e_t state;
  always_ff @(posedge clk)
    if (rst) state <= e_t'(3);
    else if (drop) state <= e_t'(3);
    else
      case (state)
        E0: if (go) state <= E1;
        E1: state <= e_t'(3);
        default: state <= E0;
      endcase
  // A value outside a wide enum is printed in hex
  typedef enum logic [39:0] {
    W0 = 40'd0,
    W1 = 40'd1
  } w_t;
  w_t wide;
  always_ff @(posedge clk)
    if (rst) wide <= W0;
    else
      case (wide)
        W0: if (go) wide <= W1;
        W1: wide <= w_t'(40'h80_0000_0000);
        default: wide <= W0;
      endcase
endmodule
