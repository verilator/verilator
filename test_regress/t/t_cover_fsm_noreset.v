// DESCRIPTION: Verilator: FSM coverage no-reset lowering test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk
);

  typedef enum logic [0:0] {
    S0 = 1'b0,
    S1 = 1'b1
  } state_t;

  int cyc;
  state_t state;

  initial begin
    cyc = 0;
    state = S0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 4) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // No reset branch on purpose: this keeps the test focused on the branch in
  // lowering that skips reset reconstruction entirely.
  always_ff @(posedge clk) begin
    case (state)
      S0: state <= S1;
      default: state <= S0;
    endcase
  end

endmodule
