// DESCRIPTION: Verilator: FSM coverage combined two-process/three-block regression
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Group supported multi-process and nearby supported-core variants so the
// main two-process / three-block extraction family stays in one place.

module fsm_basic (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S_IDLE = 2'd0,
    S_RUN = 2'd1,
    S_DONE = 2'd2,
    S_ERR = 2'd3
  } state_t;

  state_t state_q  /*verilator fsm_reset_arc*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    case (state_q)
      S_IDLE: if (start) state_d = S_RUN;
      S_RUN: state_d = S_DONE;
      default: state_d = S_ERR;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S_IDLE;
    else state_q <= state_d;
  end
endmodule

module fsm_three_block (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S_IDLE = 2'd0,
    S_BUSY = 2'd1,
    S_DONE = 2'd2
  } state_t;

  logic busy;
  logic done;
  state_t state_q;
  state_t state_d;

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

module fsm_mealy (
    input logic clk,
    input logic rst,
    input logic start,
    input logic bit_done
);
  typedef enum logic [1:0] {
    S_IDLE = 2'd0,
    S_SEND = 2'd1,
    S_DONE = 2'd2
  } state_t;

  logic tx;
  state_t state_q;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    tx = 1'b1;
    case (state_q)
      S_IDLE: begin
        if (start) begin
          state_d = S_SEND;
          tx = 1'b0;
        end
      end
      S_SEND: begin
        tx = bit_done;
        if (bit_done) state_d = S_DONE;
      end
      S_DONE: state_d = S_IDLE;
      default: state_d = S_IDLE;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S_IDLE;
    else state_q <= state_d;
  end
endmodule

module fsm_reset_policy (
    input logic clk,
    input logic rst
);
  typedef enum logic [0:0] {
    S0 = 1'b0,
    S1 = 1'b1
  } state_t;

  state_t state_incl_q  /*verilator fsm_reset_arc*/;
  state_t state_incl_d;
  state_t state_excl_q;
  state_t state_excl_d;

  always_comb begin
    state_incl_d = state_incl_q;
    case (state_incl_q)
      S0: state_incl_d = S1;
      default: state_incl_d = S1;
    endcase
  end

  always_comb begin
    state_excl_d = state_excl_q;
    case (state_excl_q)
      S0: state_excl_d = S1;
      default: state_excl_d = S1;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_incl_q <= S0;
    else state_incl_q <= state_incl_d;
  end

  always_ff @(posedge clk) begin
    if (rst) state_excl_q <= S0;
    else state_excl_q <= state_excl_d;
  end
endmodule

module fsm_nextstate_sel_off (
    input logic clk
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  state_t state_q;
  state_t state_d;

  always_comb begin
    state_d = S0;
    case (state_d)
      S0: state_d = S1;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    state_q <= state_d;
  end
endmodule

module fsm_nextstate_sel_ok (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    case (state_d)
      S0: if (start) state_d = S1;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_ternary (
    input logic clk,
    input logic rst,
    input logic sel
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = sel ? S1 : S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_plain_always (
    input logic clk,
    input logic rst,
    input logic go
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q;
  state_t state_d;

  always @* begin
    state_d = state_q;
    case (state_q)
      S0: if (go) state_d = S1;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_plain_always_list (
    input logic clk,
    input logic rst,
    input logic go
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q;
  state_t state_d;

  always @(state_q or go) begin
    state_d = state_q;
    case (state_q)
      S0: state_d = go ? S1 : S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_caseassigns_off (
    input logic clk,
    input logic rst,
    input logic go
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  logic out;
  state_t state_q;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    out = 1'b0;
    case (state_q)
      S0: out = go;
      default: out = 1'b0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_seqmix_off (
    input logic clk,
    input logic rst
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1
  } state_t;

  logic side;
  state_t state_q;
  state_t state_d;

  initial side = 1'b0;

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = S1;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else begin
      side <= ~side;
      state_q <= state_d;
    end
  end
endmodule

module t (
    input clk
);
  integer cyc;
  logic rst;
  logic start;
  logic bit_done;
  logic sel;

  fsm_basic basic_u (
      .clk(clk),
      .rst(rst),
      .start(start)
  );
  fsm_three_block three_block_u (
      .clk(clk),
      .rst(rst),
      .start(start)
  );
  fsm_mealy mealy_u (
      .clk(clk),
      .rst(rst),
      .start(start),
      .bit_done(bit_done)
  );
  fsm_reset_policy reset_u (
      .clk(clk),
      .rst(rst)
  );
  fsm_nextstate_sel_off nextstate_sel_off_u (.clk(clk));
  fsm_nextstate_sel_ok nextstate_sel_ok_u (
      .clk(clk),
      .rst(rst),
      .start(start)
  );
  fsm_ternary ternary_u (
      .clk(clk),
      .rst(rst),
      .sel(sel)
  );
  fsm_plain_always plain_always_u (
      .clk(clk),
      .rst(rst),
      .go(start)
  );
  fsm_plain_always_list plain_always_list_u (
      .clk(clk),
      .rst(rst),
      .go(start)
  );
  fsm_caseassigns_off caseassigns_off_u (
      .clk(clk),
      .rst(rst),
      .go(start)
  );
  fsm_seqmix_off seqmix_off_u (
      .clk(clk),
      .rst(rst)
  );

  initial begin
    cyc = 0;
    rst = 1'b1;
    start = 1'b0;
    bit_done = 1'b0;
    sel = 1'b0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) start <= 1'b0;
    if (cyc == 4) bit_done <= 1'b1;
    if (cyc == 4) sel <= 1'b1;
    if (cyc == 5) bit_done <= 1'b0;
    if (cyc == 5) sel <= 1'b0;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
