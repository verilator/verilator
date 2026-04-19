// DESCRIPTION: Verilator: FSM coverage same-state multi-case test
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
  state_t state /*verilator fsm_reset_arc*/;

  initial begin
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Both case statements select on the same state variable. The detector
  // should instrument both rather than warning, which covers the same-var
  // branch distinct from the existing FSMMULTI warning regression.
  always_ff @(posedge clk) begin
    if (cyc == 0) begin
      state <= S0;
    end else begin
      case (state)
        S0: state <= S1;
        default: ;
      endcase
      case (state)
        S1: state <= S2;
        default: ;
      endcase
    end
  end

endmodule
