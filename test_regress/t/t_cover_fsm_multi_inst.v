// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
// SPDX-FileCopyrightText: 2026 Wilson Snyder

module fsm(input logic clk, input logic alt);
  typedef enum logic [2:0] { IDLE, RUN1A, RUN1B, RUN2, DONE } state_t;
  state_t state;
  initial state = IDLE;
  always @(posedge clk) begin
    case (state)
      IDLE: state <= (alt ? RUN2 : RUN1A);
      RUN1A: state <= RUN1B;
      RUN1B: state <= DONE;
      RUN2: state <= DONE;
      DONE: state <= IDLE;
      default: state <= IDLE;
    endcase
  end
endmodule

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  fsm u1(.clk(clk), .alt(1'b0));
  fsm u2(.clk(clk), .alt(1'b1));

  initial begin
    #201;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
