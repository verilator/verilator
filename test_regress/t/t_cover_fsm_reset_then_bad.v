// DESCRIPTION: Verilator: FSM coverage rejects two-process reset branch with non-constant reset value
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
  logic sel;
  integer cyc;
  state_t state_q /*verilator fsm_state*/;
  state_t state_d;

  initial begin
    rst = 1'b1;
    sel = 1'b0;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) sel <= 1'b1;
    if (cyc == 3) sel <= 1'b0;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = sel ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  // Legal RTL, but unsupported for Phase 1 two-process reset matching:
  // the reset arm is not a constant state value.
  always_ff @(posedge clk) begin
    if (rst) state_q <= sel ? S0 : S1;
    else state_q <= state_d;
  end

endmodule
