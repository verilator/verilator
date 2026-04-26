// DESCRIPTION: Verilator: FSM reset arc rejects unknown enum constant
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  logic rst;
  integer cyc;
  state_t state_q /*verilator fsm_reset_arc*/;
  state_t state_d;

  initial begin
    rst = 1'b1;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = S1;
      default: state_d = S0;
    endcase
  end

  // This is a legal reset assignment, but the reset constant is outside the
  // declared enum label set. addResetArcs() must reject it via
  // validateKnownStateValue(resetArc.toValue()).
  always_ff @(posedge clk) begin
    if (rst) begin
      /* verilator lint_off ENUMVALUE */
      state_q <= 2'd3;
      /* verilator lint_on ENUMVALUE */
    end else begin
      state_q <= state_d;
    end
  end

endmodule
