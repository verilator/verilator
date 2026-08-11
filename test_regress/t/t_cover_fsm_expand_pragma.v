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

  typedef enum bit [1:0] {
    S_ERR = 2'd0,
    S_RUN = 2'd1,
    S_DONE = 2'd2,
    S_IDLE = 2'd3
  } state_t;

  typedef enum bit [2:0] {
    S2_ERR = 3'd0,
    S2_RUN = 3'd1,
    S2_DONE = 3'd2,
    S2_IDLE = 3'd3,
    S2_COMPLETING = 3'd4,
    S2_ALT_PATH = 3'd5
  } state2_t;

  bit rst;
  bit start;
  int cyc;
  state_t state  /*verilator fsm_arc_include_cond*/;
  state2_t state2  /*verilator fsm_arc_include_cond_auto*/;
  state_t state3  /*verilator fsm_arc_include_cond_auto_expand*/;
  state2_t state4  /*verilator fsm_arc_include_cond_full*/;
  state_t state5  /*verilator fsm_state*/;
  state2_t state6  /*verilator fsm_state_auto*/;
  state_t state7  /*verilator fsm_state_auto_expand*/;
  state2_t state8  /*verilator fsm_state_full*/;

  always_ff @(posedge clk) begin
    if (rst) begin
      state2 <= S2_IDLE;
    end
    else begin
      case (state2)
        S2_IDLE:
          if (start) state2 <= S2_RUN;
          else state2 <= S2_IDLE;
        S2_RUN:
          if (start) state2 <= S2_ALT_PATH;
          else state2 <= S2_COMPLETING;
        S2_COMPLETING: state2 <= S2_DONE;
        S2_DONE: state2 <= S2_DONE;
        default: state2 <= S2_ERR;
      endcase
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
      state4 <= S2_IDLE;
    end
    else begin
      case (state4)
        S2_IDLE:
          if (start) state4 <= S2_RUN;
          else state4 <= S2_IDLE;
        S2_RUN:
          if (start) state4 <= S2_ALT_PATH;
          else state4 <= S2_COMPLETING;
        S2_COMPLETING: state4 <= S2_DONE;
        S2_DONE: state4 <= S2_DONE;
        default: state4 <= S2_ERR;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state3 <= S_IDLE;
    end
    else begin
      case (state3)
        S_IDLE:
          if (start) state3 <= S_RUN;
          else state3 <= S_IDLE;
        S_RUN: state3 <= S_DONE;
        S_DONE: state3 <= S_DONE;
        default: state3 <= S_ERR;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state6 <= S2_IDLE;
    end
    else begin
      case (state6)
        S2_IDLE:
          if (start) state6 <= S2_RUN;
          else state6 <= S2_IDLE;
        S2_RUN:
          if (start) state6 <= S2_ALT_PATH;
          else state6 <= S2_COMPLETING;
        S2_COMPLETING: state6 <= S2_DONE;
        S2_DONE: state6 <= S2_DONE;
        default: state6 <= S2_ERR;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state5 <= S_IDLE;
    end
    else begin
      case (state5)
        S_IDLE:
          if (start) state5 <= S_RUN;
          else state5 <= S_IDLE;
        S_RUN: state5 <= S_DONE;
        S_DONE: state5 <= S_DONE;
        default: state5 <= S_ERR;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state8 <= S2_IDLE;
    end
    else begin
      case (state8)
        S2_IDLE:
          if (start) state8 <= S2_RUN;
          else state8 <= S2_IDLE;
        S2_RUN:
          if (start) state8 <= S2_ALT_PATH;
          else state8 <= S2_COMPLETING;
        S2_COMPLETING: state8 <= S2_DONE;
        S2_DONE: state8 <= S2_DONE;
        default: state8 <= S2_ERR;
      endcase
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state7 <= S_IDLE;
    end
    else begin
      case (state7)
        S_IDLE:
          if (start) state7 <= S_RUN;
          else state7 <= S_IDLE;
        S_RUN: state7 <= S_DONE;
        S_DONE: state7 <= S_DONE;
        default: state7 <= S_ERR;
      endcase
    end
  end

  initial begin
    `checkh(state, S_ERR);
    `checkh(state2, S2_ERR);
    `checkh(state3, S_ERR);
    `checkh(state4, S2_ERR);
    `checkh(state5, S_ERR);
    `checkh(state6, S2_ERR);
    `checkh(state7, S_ERR);
    `checkh(state8, S2_ERR);
    #20;
    `checkh(state, S_ERR);
    `checkh(state2, S2_ERR);
    `checkh(state3, S_ERR);
    `checkh(state4, S2_ERR);
    `checkh(state5, S_ERR);
    `checkh(state6, S2_ERR);
    `checkh(state7, S_ERR);
    `checkh(state8, S2_ERR);
    rst = 0;
    #20;
    `checkh(state, S_ERR);
    `checkh(state2, S2_ERR);
    `checkh(state3, S_ERR);
    `checkh(state4, S2_ERR);
    `checkh(state5, S_ERR);
    `checkh(state6, S2_ERR);
    `checkh(state7, S_ERR);
    `checkh(state8, S2_ERR);
    rst = 1;
    #20;
    `checkh(state, S_IDLE);
    `checkh(state2, S2_IDLE);
    `checkh(state3, S_IDLE);
    `checkh(state4, S2_IDLE);
    `checkh(state5, S_IDLE);
    `checkh(state6, S2_IDLE);
    `checkh(state7, S_IDLE);
    `checkh(state8, S2_IDLE);
    rst = 0;
    #20;
    `checkh(state, S_IDLE);
    `checkh(state2, S2_IDLE);
    `checkh(state3, S_IDLE);
    `checkh(state4, S2_IDLE);
    `checkh(state5, S_IDLE);
    `checkh(state6, S2_IDLE);
    `checkh(state7, S_IDLE);
    `checkh(state8, S2_IDLE);
    start = 1;
    #20;
    `checkh(state, S_RUN);
    `checkh(state2, S2_RUN);
    `checkh(state3, S_RUN);
    `checkh(state4, S2_RUN);
    `checkh(state5, S_RUN);
    `checkh(state6, S2_RUN);
    `checkh(state7, S_RUN);
    `checkh(state8, S2_RUN);
    #20;
    `checkh(state, S_DONE);
    `checkh(state2, S2_ALT_PATH);
    `checkh(state3, S_DONE);
    `checkh(state4, S2_ALT_PATH);
    `checkh(state5, S_DONE);
    `checkh(state6, S2_ALT_PATH);
    `checkh(state7, S_DONE);
    `checkh(state8, S2_ALT_PATH);
    #20;
    `checkh(state, S_DONE);
    `checkh(state2, S2_ERR);
    `checkh(state3, S_DONE);
    `checkh(state4, S2_ERR);
    `checkh(state5, S_DONE);
    `checkh(state6, S2_ERR);
    `checkh(state7, S_DONE);
    `checkh(state8, S2_ERR);


    start = 0;
    #20;
    `checkh(state, S_DONE);
    `checkh(state2, S2_ERR);
    `checkh(state3, S_DONE);
    `checkh(state4, S2_ERR);
    `checkh(state5, S_DONE);
    `checkh(state6, S2_ERR);
    `checkh(state7, S_DONE);
    `checkh(state8, S2_ERR);
    rst = 0;
    #20;
    `checkh(state, S_DONE);
    `checkh(state2, S2_ERR);
    `checkh(state3, S_DONE);
    `checkh(state4, S2_ERR);
    `checkh(state5, S_DONE);
    `checkh(state6, S2_ERR);
    `checkh(state7, S_DONE);
    `checkh(state8, S2_ERR);
    rst = 1;
    #20;
    `checkh(state, S_IDLE);
    `checkh(state2, S2_IDLE);
    `checkh(state3, S_IDLE);
    `checkh(state4, S2_IDLE);
    `checkh(state5, S_IDLE);
    `checkh(state6, S2_IDLE);
    `checkh(state7, S_IDLE);
    `checkh(state8, S2_IDLE);
    rst = 0;
    #20;
    `checkh(state, S_IDLE);
    `checkh(state2, S2_IDLE);
    `checkh(state3, S_IDLE);
    `checkh(state4, S2_IDLE);
    `checkh(state5, S_IDLE);
    `checkh(state6, S2_IDLE);
    `checkh(state7, S_IDLE);
    `checkh(state8, S2_IDLE);
    start = 1;
    #20;
    `checkh(state, S_RUN);
    `checkh(state2, S2_RUN);
    `checkh(state3, S_RUN);
    `checkh(state4, S2_RUN);
    `checkh(state5, S_RUN);
    `checkh(state6, S2_RUN);
    `checkh(state7, S_RUN);
    `checkh(state8, S2_RUN);
    start = 0;
    #20;
    `checkh(state, S_DONE);
    `checkh(state2, S2_COMPLETING);
    `checkh(state3, S_DONE);
    `checkh(state4, S2_COMPLETING);
    `checkh(state5, S_DONE);
    `checkh(state6, S2_COMPLETING);
    `checkh(state7, S_DONE);
    `checkh(state8, S2_COMPLETING);
    #20;
    `checkh(state, S_DONE);
    `checkh(state2, S2_DONE);
    `checkh(state3, S_DONE);
    `checkh(state4, S2_DONE);
    `checkh(state5, S_DONE);
    `checkh(state6, S2_DONE);
    `checkh(state7, S_DONE);
    `checkh(state8, S2_DONE);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
