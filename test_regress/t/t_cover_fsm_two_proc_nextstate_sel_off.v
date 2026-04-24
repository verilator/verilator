// DESCRIPTION: Verilator: FSM coverage ignores non-canonical case(next_state) transition blocks
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  integer cyc;
  state_t state_q;
  state_t state_d;

  initial cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 4) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always_comb begin
    state_d = S0;
    case (state_d)
      S0: state_d = S1;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    state_q <= state_d;
  end

endmodule
