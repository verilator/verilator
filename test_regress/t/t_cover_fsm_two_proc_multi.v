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

  state_t state_q  /*verilator fsm_state*/;
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

module fsm_negated_guard (
    input logic clk,
    input logic rst,
    input logic hold
);
  typedef enum logic {
    S0,
    S1
  } state_t;

  state_t state_q;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: if (!hold) state_d = S1;
      S1: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
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

  state_t state_incl_q  /*verilator fsm_state*/;
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

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = S1;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      side <= 1'b0;
      state_q <= S0;
    end
    else begin
      side <= ~side;
      state_q <= state_d;
    end
  end
endmodule

module fsm_if_chain_guard (
    input logic clk,
    input logic rst,
    input logic sel
);
  localparam logic [1:0] S0 = 2'd0;
  localparam logic [1:0] S1 = 2'd1;
  localparam logic [1:0] S2 = 2'd2;

  logic [1:0] state_q;
  logic [1:0] state_d;

  // Input guards inside the state branches of an if/else-if chain
  always_comb begin
    if (state_q == S0) begin
      if (sel) state_d = S1;
      else state_d = S2;
    end
    else if (state_q == S1) state_d = sel ? S2 : S0;
    else state_d = S0;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_if_chain_guard_noelse_off (
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

  // A nested guard without else is not a supported chain branch
  always_comb begin
    state_d = state_q;
    if (state_q == S0) begin
      if (sel) state_d = S1;
    end
    else if (state_q == S1) state_d = S2;
    else state_d = S0;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_case_guarded (
    input logic clk,
    input logic rst,
    input logic a,
    input logic b
);
  typedef enum logic [1:0] {
    S0,
    S1,
    S2,
    S3
  } state_t;

  state_t state_q;
  state_t state_d;

  // Every transition is guarded with no final else, so the default holds the state
  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: if (a) state_d = S1;
      S1:
      if (b) state_d = S2;
      else if (a) state_d = S0;
      S2: if (!a) state_d = S3;
      S3: begin
        if (a) begin
          if (b) state_d = S0;
        end
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_case_guarded_chain (
    input logic clk,
    input logic rst,
    input logic a,
    input logic b
);
  typedef enum logic [1:0] {
    S0,
    S1,
    S2
  } state_t;

  state_t state_q;
  state_t state_d;

  // S1 assigns on every path, which without coverage folds to a nested '?:',
  // so it is skipped in all forms.  S2 assigns nothing, so it has no transition.
  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: if (a) state_d = S1;
      S1:
      if (a) state_d = S2;
      else if (b) state_d = S0;
      else state_d = S1;
      S2: if (b) begin
      end
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_enable (
    input logic clk,
    input logic rst,
    input logic en
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic rst_n;
  assign rst_n = !rst;

  // Registers with an enable, which otherwise holds the state

  state_t elsif_q;
  state_t elsif_d;
  always_comb begin
    elsif_d = elsif_q;
    case (elsif_q)
      S0: elsif_d = S1;
      S1: elsif_d = S2;
      S2: elsif_d = S0;
      default: elsif_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) elsif_q <= S0;
    else if (en) elsif_q <= elsif_d;
  end

  state_t cond_q;
  state_t cond_d;
  always_comb begin
    cond_d = cond_q;
    case (cond_q)
      S0: cond_d = S1;
      S1: cond_d = S2;
      S2: cond_d = S0;
      default: cond_d = S0;
    endcase
  end
  always_ff @(posedge clk) cond_q <= rst ? S0 : (en ? cond_d : cond_q);

  state_t lowrst_q;
  state_t lowrst_d;
  always_comb begin
    lowrst_d = lowrst_q;
    case (lowrst_q)
      S0: lowrst_d = S1;
      S1: lowrst_d = S2;
      S2: lowrst_d = S0;
      default: lowrst_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (!rst_n) lowrst_q <= S0;
    else if (en) lowrst_q <= lowrst_d;
  end

  state_t noreset_q;
  state_t noreset_d;
  always_comb begin
    noreset_d = noreset_q;
    case (noreset_q)
      S0: noreset_d = S1;
      S1: noreset_d = S2;
      S2: noreset_d = S0;
      default: noreset_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (en) noreset_q <= noreset_d;
  end

  state_t noreset_cond_q;
  state_t noreset_cond_d;
  always_comb begin
    noreset_cond_d = noreset_cond_q;
    case (noreset_cond_q)
      S0: noreset_cond_d = S1;
      S1: noreset_cond_d = S2;
      S2: noreset_cond_d = S0;
      default: noreset_cond_d = S0;
    endcase
  end
  always_ff @(posedge clk) noreset_cond_q <= en ? noreset_cond_d : noreset_cond_q;

  // An enable that holds the state when set
  logic stall;
  assign stall = !en;

  state_t stall_q;
  state_t stall_d;
  always_comb begin
    stall_d = stall_q;
    case (stall_q)
      S0: stall_d = S1;
      S1: stall_d = S2;
      S2: stall_d = S0;
      default: stall_d = S0;
    endcase
  end
  always_ff @(posedge clk) stall_q <= rst ? S0 : (stall ? stall_q : stall_d);

  // Not enables, so no FSM: neither arm holds the state, or an arm is not a single value
  logic sel;
  assign sel = en;
  state_t sel_q;
  state_t a_d;
  state_t b_d;
  assign a_d = S1;
  assign b_d = S2;
  always_ff @(posedge clk) sel_q <= rst ? S0 : (sel ? a_d : b_d);
  state_t nest_q;
  always_ff @(posedge clk) nest_q <= rst ? S0 : (en ? (sel ? a_d : b_d) : nest_q);
  state_t then_q;
  always_ff @(posedge clk) then_q <= rst ? (sel ? a_d : b_d) : nest_q;
  state_t else_q;
  always_ff @(posedge clk) else_q <= rst ? S0 : (en ? else_q : (sel ? a_d : b_d));
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
  fsm_negated_guard negated_guard_u (
      .clk(clk),
      .rst(rst),
      .hold(start)
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
  fsm_if_chain_guard if_chain_guard_u (
      .clk(clk),
      .rst(rst),
      .sel(cyc[1])
  );
  fsm_if_chain_guard_noelse_off if_chain_guard_noelse_off_u (
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
  fsm_case_guarded case_guarded_u (
      .clk(clk),
      .rst(rst),
      .a(cyc[0] | cyc[1]),
      .b(cyc < 7)
  );
  fsm_case_guarded_chain case_guarded_chain_u (
      .clk(clk),
      .rst(rst),
      .a(cyc[0]),
      .b(cyc[1])
  );
  fsm_enable enable_u (
      .clk(clk),
      .rst(rst),
      .en(cyc[0])
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
