// DESCRIPTION: Verilator: FSM coverage of state registers with an enable
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 David Harris
// SPDX-License-Identifier: CC0-1.0

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
  state_t a_d;
  state_t b_d;
  assign a_d = S1;
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
      S1: reset_en_d = S2;
      S2: reset_en_d = S0;
      default: reset_en_d = S0;
    endcase
  end
  always_ff @(posedge clk) reset_en_q <= rst ? (en ? S0 : reset_en_q) : reset_en_d;

  // Not enables, so no FSM

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

  // An else that holds another register
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
endmodule

module t (
    input clk
);
  integer cyc = 0;

  fsm_enable enable_u (
      .clk(clk),
      .rst(cyc == 0),
      .en(cyc[0]),
      .sel(cyc[1])
  );

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
