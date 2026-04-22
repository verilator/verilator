// DESCRIPTION: Verilator: FSM coverage reset pseudo-vertex reuse test
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
  integer cyc;
  state_t state /*verilator fsm_reset_arc*/;

  initial begin
    rst = 1'b1;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // This reset block is intentionally non-idiomatic. The detector only collects
  // reset arcs from top-level direct assignments in the reset branch, so two
  // sequential assignments are the narrowest way to force multiple reset arcs
  // into one FSM graph and exercise reuse of the synthetic ANY reset source.
  always_ff @(posedge clk) begin
    if (rst) begin
      state <= S0;
      state <= S1;
    end else begin
      case (state)
        S0: state <= S2;
        S1: state <= S2;
        default: state <= S2;
      endcase
    end
  end

endmodule
