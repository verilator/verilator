// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

package P;
  typedef struct packed{
    logic [7:0] vs;
  } C;
  typedef struct packed{
    C a; int b;
  } B;
  typedef struct packed{
    B a;
  } A;
endpackage

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
  state_t state  /*verilator fsm_reset_arc*/;
  P::A a;
  logic done;

  logic [7:0] va[int];
  logic [7:0] va2d[int][int];

  logic b;
  logic c;
  logic d;

  assign b = (a.a.a.vs == 8'h0);
  assign c = (va[0] == 8'h0);
  assign d = (va2d[0][0] == 8'h0);

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
        S_RUN: begin
          a.a.a.vs <= a.a.a.vs + 1;
          done <= (a.a.a.vs == 8'h1);
          if (done) begin
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
