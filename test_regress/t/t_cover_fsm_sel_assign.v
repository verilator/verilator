// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t #(
  parameter int unsigned W = 16,
  parameter int unsigned D = 4,
  parameter int unsigned BW = 2
) (
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
  state_t state  /*verilator fsm_reset_arc*/;
  logic [1:0] done_arr;

  logic [W-1:0] a;
  logic [BW-1:0] b;
  begin
    logic [D-1:0][W-1:0] s;
    begin
      always_ff @(posedge clk)
      s[b] <= a;
    end
  end

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
    if (cyc == 4) a[0] = 1'b1;
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
        S_RUN: begin;
          done_arr[0] <= (a[0] == 1'b1);
          if (done_arr[0]) begin
              state <= S_DONE;
          end else begin
              state <= S_RUN;
          end
        end
        S_DONE: state <= S_DONE;
        default: state <= S_ERR;
      endcase
    end
  end

endmodule
