// DESCRIPTION: Verilator: FSM coverage negative extraction test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk
);

  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  int cyc;
  logic side;
  state_t state /*verilator fsm_reset_arc*/;

  initial begin
    cyc = 0;
    side = 1'b0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) side <= 1'b1;
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // The S0 arm is the supported baseline. The S1 and default arms are
  // deliberately unsupported extractor shapes: one has two meaningful
  // statements, the other writes a different lhs first. Coverage should ignore
  // those arcs rather than guessing.
  always_ff @(posedge clk) begin
    if (cyc == 0) begin
      state <= S0;
    end else begin
      case (state)
        S0: state <= S1;
        S1: begin
          side <= ~side;
          state <= S2;
        end
        default: begin
          side <= 1'b0;
          state <= S0;
        end
      endcase
    end
  end

endmodule
