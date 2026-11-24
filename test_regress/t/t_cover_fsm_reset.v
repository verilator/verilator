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
