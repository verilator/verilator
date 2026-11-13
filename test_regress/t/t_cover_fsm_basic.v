// DESCRIPTION: Verilator: FSM coverage basic test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  typedef enum logic [1:0] {
    S_IDLE = 2'd0,
    S_RUN = 2'd1,
    S_DONE = 2'd2,
    S_ERR = 2'd3
  } state_t;

  logic rst;
  logic start;
  integer cyc;
  state_t state  /*verilator fsm_state*/;
  // Resets to H_RUN and 0 isn't a state, so nothing is entered before the reset
  typedef enum logic [1:0] {
    H_RUN = 2'd1,
    H_DONE = 2'd2,
    H_IDLE = 2'd3
  } hi_t;
  hi_t state_hi  /*verilator fsm_state_full*/;

  initial begin
    rst = 1'b1;
    start = 1'b0;
    cyc = 0;
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

  always_ff @(posedge clk) begin
    if (rst) begin
      state <= S_IDLE;
    end
    else begin
      case (state)
        S_IDLE:
        if (start) state <= S_RUN;
        else state <= S_IDLE;
        S_RUN: state <= S_DONE;
        S_DONE: state <= S_DONE;
        default: state <= S_ERR;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state_hi <= H_RUN;
    end
    else begin
      case (state_hi)
        H_IDLE: state_hi <= H_RUN;
        H_RUN: state_hi <= H_DONE;
        H_DONE: state_hi <= H_DONE;
        default: state_hi <= H_IDLE;
      endcase
    end
  end

  // Given a value at time 0, so that value is the first state, as without a reset
  hi_t state_decl = H_IDLE;
  always_ff @(posedge clk) begin
    if (rst) begin
      state_decl <= H_RUN;
    end
    else begin
      case (state_decl)
        H_IDLE: state_decl <= H_RUN;
        H_RUN: state_decl <= H_DONE;
        default: state_decl <= H_IDLE;
      endcase
    end
  end

  // An initial block may also give it (always_ff state can't be written by another process).
  // Its time-0 value isn't counted, as the coverage sample runs before this initial block.
  hi_t state_init;
  initial state_init = H_IDLE;
  always @(posedge clk) begin
    if (rst) begin
      state_init <= H_RUN;
    end
    else begin
      case (state_init)
        H_IDLE: state_init <= H_RUN;
        H_RUN: state_init <= H_DONE;
        default: state_init <= H_IDLE;
      endcase
    end
  end

endmodule
