// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: on
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: off

module t;
  bit clk;
  assign #10 clk = ~clk;

  typedef enum bit [999:0] {
    S_ERR = 1000'd0,
    S_RUN = 1000'd1,
    S_DONE = 1000'd2,
    S_IDLE = 1000'd3
  } state_t;

  bit rst;
  bit start;
  int cyc;
  state_t state  /*verilator fsm_arc_include_cond*/;

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
endmodule
