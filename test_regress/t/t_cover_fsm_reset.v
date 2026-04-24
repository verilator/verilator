// DESCRIPTION: Verilator: FSM coverage reset policy test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  typedef enum logic [0:0] {
    S0 = 1'b0,
    S1 = 1'b1
  } state_t;

  logic rst;
  integer cyc;
  state_t state_incl  /*verilator fsm_reset_arc*/;
  state_t state_excl;

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

  always_ff @(posedge clk) begin
    if (rst) state_incl <= S0;
    else
      case (state_incl)
        S0: state_incl <= S1;
        default: state_incl <= S1;
      endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_excl <= S0;
    else
      case (state_excl)
        S0: state_excl <= S1;
        default: state_excl <= S1;
      endcase
  end

endmodule
