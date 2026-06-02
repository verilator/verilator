// DESCRIPTION: Verilator: Runtime hierarchy coverage data for report tests
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module fsm_core (
    input  logic clk,
    input  logic rst,
    input  logic start,
    input  logic finish,
    input  logic fail,
    input  logic retry
);
  typedef enum logic [2:0] {
    S_IDLE = 3'd0,
    S_LOAD = 3'd1,
    S_RUN  = 3'd2,
    S_WAIT = 3'd3,
    S_DONE = 3'd4,
    S_ERR  = 3'd5
  } state_t;

  state_t state_q /*verilator fsm_reset_arc*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    case (state_q)
      S_IDLE: if (start) state_d = S_LOAD;
      S_LOAD: state_d = S_RUN;
      S_RUN: begin
        if (fail) state_d = S_ERR;
        else if (finish) state_d = S_DONE;
        else state_d = S_WAIT;
      end
      S_WAIT: begin
        if (finish) state_d = S_DONE;
        else state_d = S_RUN;
      end
      S_DONE: state_d = S_IDLE;
      S_ERR: begin
        if (retry) state_d = S_LOAD;
        else state_d = S_ERR;
      end
      default: state_d = S_ERR;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S_IDLE;
    else state_q <= state_d;
  end
endmodule

module cluster #(
    parameter int MODE = 0
) (
    input logic clk,
    input logic rst
);
  logic [4:0] cyc = 0;
  logic start;
  logic finish;
  logic fail;
  logic retry;

  always_ff @(posedge clk) begin
    if (rst) cyc <= 0;
    else cyc <= cyc + 1'b1;
  end

  always_comb begin
    start = 1'b0;
    finish = 1'b0;
    fail = 1'b0;
    retry = 1'b0;
    if (MODE == 0) begin
      start = (cyc == 1) || (cyc == 7);
      finish = (cyc == 4) || (cyc == 10);
    end else begin
      start = (cyc == 1);
      fail = (cyc == 3);
      retry = (cyc == 6);
      finish = (cyc == 9);
    end
  end

  fsm_core u_core (
      .clk(clk),
      .rst(rst),
      .start(start),
      .finish(finish),
      .fail(fail),
      .retry(retry)
  );
endmodule

module tb;
  logic clk = 0;
  logic rst = 1;
  int cyc = 0;

  always #1 clk = !clk;

  always_ff @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 0;
    if (cyc == 14) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  cluster #(.MODE(0)) cluster_a (.clk(clk), .rst(rst));
  cluster #(.MODE(1)) cluster_b (.clk(clk), .rst(rst));
endmodule
