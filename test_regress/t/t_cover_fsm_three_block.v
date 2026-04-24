// DESCRIPTION: Verilator: FSM coverage three-block FSM test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  typedef enum logic [1:0] {
    S_IDLE = 2'd0,
    S_BUSY = 2'd1,
    S_DONE = 2'd2
  } state_t;

  integer cyc;
  logic rst;
  logic start;
  logic busy;
  logic done;
  state_t state_q;
  state_t state_d;

  initial begin
    cyc = 0;
    rst = 1'b1;
    start = 1'b0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) start <= 1'b0;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always_comb begin
    state_d = state_q;
    case (state_q)
      S_IDLE: if (start) state_d = S_BUSY;
      S_BUSY: state_d = S_DONE;
      S_DONE: state_d = S_IDLE;
      default: state_d = S_IDLE;
    endcase
  end

  always_comb begin
    busy = (state_q == S_BUSY);
    done = (state_q == S_DONE);
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S_IDLE;
    else state_q <= state_d;
  end

endmodule
