// DESCRIPTION: Verilator: FSM coverage ignores forced non-enum state variables that are too wide
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  integer cyc;
  logic rst;
  logic [30:0] state  /*verilator fsm_state*/;

  initial begin
    cyc = 0;
    rst = 1'b1;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 6) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state <= 31'd0;
    end else begin
      case (state)
        31'd0: state <= 31'd1;
        31'd1: state <= 31'd2;
        default: state <= 31'd0;
      endcase
    end
  end

endmodule
