// DESCRIPTION: Verilator: FSM coverage grouped reset semantics test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Group accepted simulator-style reset semantics, including reset include /
// exclude behavior and nearby fallback cases that should still preserve FSMs.

module fsm_reset_policy (
    input logic clk,
    input logic rst
);

  typedef enum logic [0:0] {
    S0 = 1'b0,
    S1 = 1'b1
  } state_t;

  state_t state_incl  /*verilator fsm_state*/;
  state_t state_excl;

  always_ff @(posedge clk) begin
    if (rst) state_incl <= S0;
    else
      case (state_incl)
        S0: state_incl <= S1;
        default: state_incl <= S1;
      endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_excl <= S0;
    else
      case (state_excl)
        S0: state_excl <= S1;
        default: state_excl <= S1;
      endcase
  end
endmodule

module fsm_reset_other_assign_ok (
    input logic clk,
    input logic rst
);
  typedef enum logic [1:0] {
    S0 = 2'b00,
    S1 = 2'b01,
    S2 = 2'b10
  } state_t;

  logic aux;
  logic start;
  state_t state_q;
  state_t state_d;

  always_ff @(posedge clk) begin
    if (rst) begin
      aux <= 1'b1;
      start <= 1'b1;
      state_q <= S0;
      aux <= 1'b0;
    end
    else begin
      state_q <= state_d;
    end
  end

  always_comb begin
    state_d = state_q;
    case (state_q)
      S0: state_d = start ? S1 : S2;
      default: state_d = S0;
    endcase
  end
endmodule

module fsm_oneblock_reset_mismatch_ok (
    input logic clk,
    input logic rst
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q = S0;
  state_t other_q = S2;

  always_ff @(posedge clk) begin
    if (rst) begin
      other_q <= S0;
    end
    else begin
      case (state_q)
        S0: state_q <= S1;
        default: state_q <= S2;
      endcase
    end
  end
endmodule

module fsm_oneblock_reset_nonconst_ok (
    input logic clk,
    input logic rst
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q = S0;
  state_t other_q = S2;

  // Useful because the one-block reset fallback must ignore non-constant reset
  // assignments and still retain the supported case(state_q) FSM below.
  always_ff @(posedge clk) begin
    if (rst) begin
      state_q <= other_q;
    end
    else begin
      case (state_q)
        S0: state_q <= S1;
        default: state_q <= S2;
      endcase
    end
  end
endmodule

module fsm_reset_active_low (
    input logic clk,
    input logic rst_n
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t sync_q;
  state_t sync_d;
  state_t async_q;
  state_t async_d;
  state_t oneblock_q;
  state_t tern_q;
  state_t tern_d;
  state_t chain_q;
  logic [1:0] count;
  logic busy;

  // V3Const writes 'if (!rst_n) R; else C' as 'if (rst_n) C; else R', and without other
  // coverage folds this one into 'sync_q <= rst_n ? sync_d : S0'
  always_ff @(posedge clk) begin
    if (!rst_n) sync_q <= S0;
    else sync_q <= sync_d;
  end

  // Branch coverage lifts the '?:' into an if/else on a temporary
  always_ff @(posedge clk) begin
    tern_q <= !rst_n ? S0 : tern_d;
  end

  always_comb begin
    tern_d = tern_q;
    case (tern_q)
      S0: tern_d = S1;
      S1: tern_d = S2;
      default: tern_d = S0;
    endcase
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      async_q <= S0;
      count <= '0;
    end
    else begin
      async_q <= async_d;
      count <= count + 1'b1;
    end
  end

  always_comb begin
    sync_d = sync_q;
    case (sync_q)
      S0: sync_d = S1;
      S1: sync_d = S2;
      default: sync_d = S0;
    endcase
  end

  always_comb begin
    async_d = async_q;
    case (async_q)
      S0: async_d = S1;
      S1: async_d = S2;
      default: async_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) oneblock_q <= S0;
    else
      case (oneblock_q)
        S0: oneblock_q <= S1;
        S1: oneblock_q <= S2;
        default: oneblock_q <= S0;
      endcase
  end

  // Two statements per branch keep the chain from folding into one assignment
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      chain_q <= S0;
      busy <= 1'b0;
    end
    else if (chain_q == S0) begin
      chain_q <= S1;
      busy <= 1'b1;
    end
    else if (chain_q == S1) begin
      chain_q <= S2;
      busy <= 1'b1;
    end
    else begin
      chain_q <= S0;
      busy <= 1'b0;
    end
  end
endmodule

module fsm_enable (
    input logic clk,
    input logic rst,
    input logic en,
    input logic sel
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;
  logic rst_n;
  assign rst_n = !rst;
  logic stall;
  assign stall = !en;
  state_t b_d;
  assign b_d = S2;

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

  state_t lowcond_q;
  state_t lowcond_d;
  always_comb begin
    lowcond_d = lowcond_q;
    case (lowcond_q)
      S0: lowcond_d = S1;
      S1: lowcond_d = S2;
      S2: lowcond_d = S0;
      default: lowcond_d = S0;
    endcase
  end
  always_ff @(posedge clk) lowcond_q <= rst_n ? (en ? lowcond_d : lowcond_q) : S0;

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

  state_t hold_q;
  state_t hold_d;
  always_comb begin
    hold_d = hold_q;
    case (hold_q)
      S0: hold_d = S1;
      S1: hold_d = S2;
      S2: hold_d = S0;
      default: hold_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) hold_q <= S0;
    else if (en) hold_q <= hold_d;
    else hold_q <= hold_q;
  end

  state_t noreset_hold_q;
  state_t noreset_hold_d;
  always_comb begin
    noreset_hold_d = noreset_hold_q;
    case (noreset_hold_q)
      S0: noreset_hold_d = S1;
      S1: noreset_hold_d = S2;
      S2: noreset_hold_d = S0;
      default: noreset_hold_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (en) noreset_hold_q <= noreset_hold_d;
    else noreset_hold_q <= noreset_hold_q;
  end

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

  state_t stall_if_q;
  state_t stall_if_d;
  always_comb begin
    stall_if_d = stall_if_q;
    case (stall_if_q)
      S0: stall_if_d = S1;
      S1: stall_if_d = S2;
      S2: stall_if_d = S0;
      default: stall_if_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) stall_if_q <= S0;
    else if (stall) stall_if_q <= stall_if_q;
    else stall_if_q <= stall_if_d;
  end

  state_t nest_cond_q;
  state_t nest_cond_d;
  always_comb begin
    nest_cond_d = nest_cond_q;
    case (nest_cond_q)
      S0: nest_cond_d = S1;
      S1: nest_cond_d = S2;
      S2: nest_cond_d = S0;
      default: nest_cond_d = S0;
    endcase
  end
  always_ff @(posedge clk)
    nest_cond_q <= rst ? S0 : (en ? (sel ? nest_cond_d : nest_cond_q) : nest_cond_q);

  state_t nest_if_q;
  state_t nest_if_d;
  always_comb begin
    nest_if_d = nest_if_q;
    case (nest_if_q)
      S0: nest_if_d = S1;
      S1: nest_if_d = S2;
      S2: nest_if_d = S0;
      default: nest_if_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) nest_if_q <= S0;
    else if (en) begin
      if (sel) nest_if_q <= nest_if_d;
    end
  end

  state_t reset_en_q;
  state_t reset_en_d;
  always_comb begin
    reset_en_d = reset_en_q;
    case (reset_en_q)
      S0: reset_en_d = S1;
      S1: if (en) reset_en_d = S2;
      S2: reset_en_d = S0;
      default: reset_en_d = S0;
    endcase
  end
  always_ff @(posedge clk) reset_en_q <= rst ? (en ? S0 : reset_en_q) : reset_en_d;

  state_t arm_cond_q;
  state_t arm_cond_d;
  always_comb begin
    arm_cond_d = arm_cond_q;
    case (arm_cond_q)
      S0: arm_cond_d = S1;
      S1: arm_cond_d = S2;
      S2: arm_cond_d = S0;
      default: arm_cond_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) arm_cond_q <= S0;
    else arm_cond_q <= en ? arm_cond_d : arm_cond_q;
  end

  state_t reset_two_q;
  state_t reset_two_d;
  always_comb begin
    reset_two_d = reset_two_q;
    case (reset_two_q)
      S0: reset_two_d = S1;
      S1: reset_two_d = S2;
      S2: reset_two_d = S0;
      default: reset_two_d = S0;
    endcase
  end
  logic reset_two_x;
  always_ff @(posedge clk) begin
    if (rst) begin
      reset_two_q <= S0;
      reset_two_x <= 1'b0;
    end
    else if (en) reset_two_q <= reset_two_d;
    else reset_two_q <= reset_two_q;
  end

  state_t stall_noreset_q;
  state_t stall_noreset_d;
  always_comb begin
    stall_noreset_d = stall_noreset_q;
    case (stall_noreset_q)
      S0: stall_noreset_d = S1;
      S1: stall_noreset_d = S2;
      S2: stall_noreset_d = S0;
      default: stall_noreset_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (stall) stall_noreset_q <= stall_noreset_q;
    else stall_noreset_q <= stall_noreset_d;
  end

  state_t en_cond_q;
  state_t en_cond_d;
  always_comb begin
    en_cond_d = en_cond_q;
    case (en_cond_q)
      S0: en_cond_d = S1;
      S1: en_cond_d = S2;
      S2: en_cond_d = S0;
      default: en_cond_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) en_cond_q <= S0;
    else if (en) en_cond_q <= sel ? en_cond_d : en_cond_q;
  end

  state_t if_en_cond_q;
  state_t if_en_cond_d;
  always_comb begin
    if_en_cond_d = if_en_cond_q;
    case (if_en_cond_q)
      S0: if_en_cond_d = S1;
      S1: if_en_cond_d = S2;
      S2: if_en_cond_d = S0;
      default: if_en_cond_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (en) if_en_cond_q <= sel ? if_en_cond_d : if_en_cond_q;
  end

  // An enabled commit of several statements, as an else commit may be
  state_t then_two_q;
  state_t then_two_d;
  always_comb begin
    then_two_d = then_two_q;
    case (then_two_q)
      S0: then_two_d = S1;
      S1: then_two_d = S2;
      S2: then_two_d = S0;
      default: then_two_d = S0;
    endcase
  end
  logic then_two_x;
  always_ff @(posedge clk) begin
    if (en) begin
      then_two_q <= then_two_d;
      then_two_x <= 1'b1;
    end
  end

  state_t reset_two_en_q;
  state_t reset_two_en_d;
  always_comb begin
    reset_two_en_d = reset_two_en_q;
    case (reset_two_en_q)
      S0: reset_two_en_d = S1;
      S1: reset_two_en_d = S2;
      S2: reset_two_en_d = S0;
      default: reset_two_en_d = S0;
    endcase
  end
  logic [3:0] reset_two_en_cnt;
  always_ff @(posedge clk) begin
    if (rst) begin
      reset_two_en_q <= S0;
      reset_two_en_cnt <= '0;
    end
    else if (en) begin
      reset_two_en_q <= reset_two_en_d;
      reset_two_en_cnt <= reset_two_en_cnt + 4'd1;
    end
  end

  // An explicit hold beside a conditional commit
  state_t hold_cond_q;
  state_t hold_cond_d;
  always_comb begin
    hold_cond_d = hold_cond_q;
    case (hold_cond_q)
      S0: hold_cond_d = S1;
      S1: hold_cond_d = S2;
      S2: hold_cond_d = S0;
      default: hold_cond_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) hold_cond_q <= S0;
    else if (en) hold_cond_q <= sel ? hold_cond_d : hold_cond_q;
    else hold_cond_q <= hold_cond_q;
  end

  // Not enables, or unsupported ones, so no FSM

  // An enabled commit whose first statement is not the state's: only the first is matched
  state_t order_q;
  state_t order_d;
  always_comb begin
    order_d = order_q;
    case (order_q)
      S0: order_d = S1;
      S1: order_d = S2;
      S2: order_d = S0;
      default: order_d = S0;
    endcase
  end
  logic [3:0] order_cnt;
  always_ff @(posedge clk) begin
    if (en) begin
      order_cnt <= order_cnt + 4'd1;
      order_q <= order_d;
    end
  end

  // An enabled commit that writes the state again
  state_t twice_q;
  state_t twice_d;
  always_comb begin
    twice_d = twice_q;
    case (twice_q)
      S0: twice_d = S1;
      S1: twice_d = S2;
      S2: twice_d = S0;
      default: twice_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (en) begin
      twice_q <= twice_d;
      if (rst) twice_q <= S0;
    end
  end

  // A reset arm whose first statement holds another register is still a reset
  state_t reset_hold_q;
  state_t reset_hold_d;
  always_comb begin
    reset_hold_d = reset_hold_q;
    case (reset_hold_q)
      S0: reset_hold_d = S1;
      S1: reset_hold_d = S2;
      S2: reset_hold_d = S0;
      default: reset_hold_d = S0;
    endcase
  end
  logic reset_hold_x;
  always_ff @(posedge clk) begin
    if (en) reset_hold_q <= reset_hold_d;
    else begin
      reset_hold_x <= reset_hold_x;
      reset_hold_q <= S0;
    end
  end

  // Neither arm holds the state
  state_t neither_q;
  state_t neither_d;
  always_comb begin
    neither_d = neither_q;
    case (neither_q)
      S0: neither_d = S1;
      S1: neither_d = S2;
      S2: neither_d = S0;
      default: neither_d = S0;
    endcase
  end
  always_ff @(posedge clk) neither_q <= rst ? S0 : (sel ? neither_d : b_d);

  // An inner enable whose arms do not hold the state
  state_t nest_neither_q;
  state_t nest_neither_d;
  always_comb begin
    nest_neither_d = nest_neither_q;
    case (nest_neither_q)
      S0: nest_neither_d = S1;
      S1: nest_neither_d = S2;
      S2: nest_neither_d = S0;
      default: nest_neither_d = S0;
    endcase
  end
  always_ff @(posedge clk)
    nest_neither_q <= rst ? S0 : (en ? (sel ? nest_neither_d : b_d) : nest_neither_q);

  // A reset arm that is not a constant
  state_t a_d;
  assign a_d = S1;
  state_t reset_sel_q;
  state_t reset_sel_d;
  always_comb begin
    reset_sel_d = reset_sel_q;
    case (reset_sel_q)
      S0: reset_sel_d = S1;
      S1: reset_sel_d = S2;
      S2: reset_sel_d = S0;
      default: reset_sel_d = S0;
    endcase
  end
  always_ff @(posedge clk) reset_sel_q <= rst ? (sel ? a_d : b_d) : reset_sel_d;

  // An else that loads the state from another register
  state_t other_hold_q;
  state_t other_hold_d;
  always_comb begin
    other_hold_d = other_hold_q;
    case (other_hold_q)
      S0: other_hold_d = S1;
      S1: other_hold_d = S2;
      S2: other_hold_d = S0;
      default: other_hold_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (en) other_hold_q <= other_hold_d;
    else other_hold_q <= hold_q;
  end

  // A next state that is not a single value
  state_t then_hold_q;
  state_t then_hold_d;
  always_comb begin
    then_hold_d = then_hold_q;
    case (then_hold_q)
      S0: then_hold_d = S1;
      S1: then_hold_d = S2;
      S2: then_hold_d = S0;
      default: then_hold_d = S0;
    endcase
  end
  always_ff @(posedge clk) then_hold_q <= rst ? S0 : (en ? then_hold_q : (sel ? then_hold_d : b_d));

  // An enable on the reset arm as an if, unlike the conditional form of reset_en_q
  state_t reset_if_en_q;
  state_t reset_if_en_d;
  always_comb begin
    reset_if_en_d = reset_if_en_q;
    case (reset_if_en_q)
      S0: reset_if_en_d = S1;
      S1: reset_if_en_d = S2;
      S2: reset_if_en_d = S0;
      default: reset_if_en_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) begin
      if (en) reset_if_en_q <= S0;
    end
    else reset_if_en_q <= reset_if_en_d;
  end

  // A commit that loads a constant, not an enable
  state_t load_q;
  state_t load_d;
  always_comb begin
    load_d = load_q;
    case (load_q)
      S0: load_d = S1;
      S1: load_d = S2;
      S2: load_d = S0;
      default: load_d = S0;
    endcase
  end
  always_ff @(posedge clk) begin
    if (rst) load_q <= S0;
    else load_q <= sel ? S1 : load_d;
  end
endmodule

module t (
    input logic clk
);

  logic rst;
  integer cyc;

  fsm_reset_policy reset_policy_u (
      .clk(clk),
      .rst(rst)
  );
  fsm_reset_other_assign_ok reset_other_assign_ok_u (
      .clk(clk),
      .rst(rst)
  );
  fsm_oneblock_reset_mismatch_ok oneblock_reset_mismatch_ok_u (
      .clk(clk),
      .rst(rst)
  );
  fsm_oneblock_reset_nonconst_ok oneblock_reset_nonconst_ok_u (
      .clk(clk),
      .rst(rst)
  );
  // A second reset at cyc 4 from S1 hits the reset arcs; the enable is off once, at cyc 3
  fsm_enable enable_u (
      .clk(clk),
      .rst(rst || cyc == 4),
      .en(cyc != 3),
      .sel(cyc[0] || cyc == 2)
  );
  // A second reset from S1 hits the active-low FSMs' reset arc S1->S0, which their
  // next-state logic never takes
  fsm_reset_active_low reset_active_low_u (
      .clk(clk),
      .rst_n(!rst && cyc != 6)
  );

  initial begin
    rst = 1'b1;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
