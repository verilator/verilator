// DESCRIPTION: Verilator: FSM coverage ignores mixed register logic in two-process form
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
  logic rst;
  logic side;
  state_t state_q;
  state_t state_d;

  initial begin
    cyc = 0;
    rst = 1'b1;
    side = 1'b0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 4) begin
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

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else begin
      side <= ~side;
      state_q <= state_d;
    end
  end

endmodule
