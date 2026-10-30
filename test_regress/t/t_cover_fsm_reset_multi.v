// DESCRIPTION: Verilator: FSM coverage multi-reset assignment warning test
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
  state_t state  /*verilator fsm_state*/;
  state_t state_folded  /*verilator fsm_state*/;

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

  // This reset block is intentionally non-idiomatic. Multiple assignments to
  // the FSM state variable in the reset branch should warn and be ignored for
  // reset-arc extraction rather than inventing multiple reset transitions.
  always_ff @(posedge clk) begin
    if (rst) begin
      state <= S0;
      state <= S1;
    end
    else begin
      case (state)
        S0: state <= S2;
        S1: state <= S2;
        default: state <= S2;
      endcase
    end
  end

  // Folding this if leaves a coverage counter between the reset assignments.
  // The second assignment must still trigger the multiple-assignment warning.
  always_ff @(posedge clk) begin
    if (rst) begin
      state_folded <= S0;
      if (1'b1) state_folded <= S1;
    end
    else begin
      case (state_folded)
        S0: state_folded <= S2;
        S1: state_folded <= S2;
        default: state_folded <= S2;
      endcase
    end
  end

endmodule
