// DESCRIPTION: Verilator: FSM coverage ignores plain always cases that do not assign next-state
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic rst;
  logic start;
  logic other;
  integer cyc;
  state_t state_q /*verilator fsm_reset_arc*/;
  state_t state_d;

  initial begin
    rst = 1'b1;
    start = 1'b0;
    other = 1'b0;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) start <= 1'b0;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // The selector matches the FSM state, but the case body never assigns
  // state_d, so the warning scan should ignore it.
  always @(posedge clk) begin
    state_d = state_q;
    case (state_q)
      S0: other = start;
      default: other = 1'b0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state_q <= S0;
    end else begin
      state_q <= state_d;
    end
  end

endmodule
