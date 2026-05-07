// DESCRIPTION: Verilator: FSM coverage detects if/else-chain FSM dispatch
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module fsm_if_enum_oneblock (
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

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else if (state_q == S0) state_q <= start ? S1 : S0;
    else if (state_q == S1) state_q <= S2;
    else if (state_q == S2) state_q <= S0;
  end
endmodule

module fsm_if_enum_twoproc (
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
    if (state_q == S0) state_d = start ? S1 : S0;
    else if (state_q == S1) state_d = S2;
    else if (state_q == S2) state_d = S0;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_if_localparam (
    input logic clk,
    input logic rst,
    input logic start
);
  localparam logic [1:0] IDLE = 2'd0;
  localparam logic [1:0] BUSY = 2'd1;
  localparam logic [1:0] DONE = 2'd2;

  logic [1:0] state_q;
  logic [1:0] state_d;

  always_comb begin
    state_d = state_q;
    if (state_q == IDLE) state_d = start ? BUSY : IDLE;
    else if (state_q == BUSY) state_d = DONE;
    else if (state_q == DONE) state_d = IDLE;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= IDLE;
    else state_q <= state_d;
  end
endmodule

module fsm_if_parameter #(
    parameter logic [1:0] IDLE = 2'd0,
    parameter logic [1:0] BUSY = 2'd1,
    parameter logic [1:0] DONE = 2'd2
) (
    input logic clk,
    input logic rst,
    input logic start
);
  logic [1:0] state_q;
  logic [1:0] state_d;

  always_comb begin
    state_d = state_q;
    if (state_q == IDLE) state_d = start ? BUSY : IDLE;
    else if (state_q == BUSY) state_d = DONE;
    else if (state_q == DONE) state_d = IDLE;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= IDLE;
    else state_q <= state_d;
  end
endmodule

module fsm_if_literal_forced (
    input logic clk,
    input logic rst
);
  logic [1:0] state  /*verilator fsm_state*/;

  always_ff @(posedge clk) begin
    if (rst) state <= 2'd0;
    else if (state == 2'd0) state <= 2'd1;
    else if (state == 2'd1) state <= 2'd2;
    else if (state == 2'd2) state <= 2'd0;
  end
endmodule

module fsm_if_guard_state_first (
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
    if ((state_q == S0) && start) state_d = S1;
    else if (state_q == S1) state_d = S2;
    else if (state_q == S2) state_d = S0;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_if_guard_first (
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
    if (start && (state_q == S0)) state_d = S1;
    else if (state_q == S1) state_d = S2;
    else if (state_q == S2) state_d = S0;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_if_local_alias (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic idle_state;
  state_t state_q;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    idle_state = (state_q == S0);
    if (idle_state && start) state_d = S1;
    else if (state_q == S1) state_d = S2;
    else if (state_q == S2) state_d = S0;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_if_continuous_alias (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic idle_state;
  state_t state_q;
  state_t state_d;

  assign idle_state = (state_q == S0);

  always_comb begin
    state_d = state_q;
    if (idle_state && start) state_d = S1;
    else if (state_q == S1) state_d = S2;
    else if (state_q == S2) state_d = S0;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_if_nested_bitand_guard (
    input logic clk,
    input logic rst,
    input logic start,
    input logic choose
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
    if ((state_q == S0) & start) begin
      if (choose) state_d = S1;
      else state_d = S0;
    end else if (state_q == S1) state_d = S2;
    else if (state_q == S2) state_d = S0;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_if_default_incl (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q  /*verilator fsm_arc_include_cond*/;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    if (state_q == S0) state_d = start ? S1 : S0;
    else if (state_q == S1) state_d = S2;
    else state_d = S0;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_if_oneblock_late_continuous_alias (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic idle_state;
  state_t state_q;

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else if (idle_state && start) state_q <= S1;
    else if (state_q == S1) state_q <= S2;
    else if (state_q == S2) state_q <= S0;
  end

  assign idle_state = (state_q == S0);
endmodule

module fsm_if_nextstate_compare (
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
    if (state_d == S0) state_d = start ? S1 : S0;
    else if (state_d == S1) state_d = S2;
    else if (state_d == S2) state_d = S0;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_if_reversed_compare (
    input logic clk,
    input logic rst
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q;

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else if (S0 == state_q) state_q <= S1;
    else if (S1 == state_q) state_q <= S2;
    else if (S2 == state_q) state_q <= S0;
  end
endmodule

module fsm_if_duplicate_alias (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  logic idle_state;
  state_t state_q;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    idle_state = (state_q == S0);
    idle_state = (state_q == S0);
    if (idle_state && start) state_d = S1;
    else if (state_q == S1) state_d = S2;
    else if (state_q == S2) state_d = S0;
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_if_case_priority (
    input logic clk,
    input logic rst
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2
  } state_t;

  state_t state_q;
  state_t state_d;
  state_t other_q;
  state_t other_d;

  always_comb begin
    state_d = state_q;
    other_d = other_q;
    case (state_q)
      S0: state_d = S1;
      S1: state_d = S2;
      S2: state_d = S0;
      default: state_d = state_q;
    endcase
    if (other_q == S0) other_d = S1;
    else if (other_q == S1) other_d = S2;
    else if (other_q == S2) other_d = S0;
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state_q <= S0;
      other_q <= S0;
    end else begin
      state_q <= state_d;
      other_q <= other_d;
    end
  end
endmodule

module t (
    input logic clk
);
  logic rst;
  logic start;
  logic choose;
  integer cyc;

  fsm_if_enum_oneblock enum_oneblock_u (.clk(clk), .rst(rst), .start(start));
  fsm_if_enum_twoproc enum_twoproc_u (.clk(clk), .rst(rst), .start(start));
  fsm_if_localparam localparam_u (.clk(clk), .rst(rst), .start(start));
  fsm_if_parameter parameter_u (.clk(clk), .rst(rst), .start(start));
  fsm_if_literal_forced literal_forced_u (.clk(clk), .rst(rst));
  fsm_if_guard_state_first guard_state_first_u (.clk(clk), .rst(rst), .start(start));
  fsm_if_guard_first guard_first_u (.clk(clk), .rst(rst), .start(start));
  fsm_if_local_alias local_alias_u (.clk(clk), .rst(rst), .start(start));
  fsm_if_continuous_alias continuous_alias_u (.clk(clk), .rst(rst), .start(start));
  fsm_if_nested_bitand_guard nested_bitand_guard_u (
      .clk(clk), .rst(rst), .start(start), .choose(choose));
  fsm_if_default_incl default_incl_u (.clk(clk), .rst(rst), .start(start));
  fsm_if_oneblock_late_continuous_alias oneblock_late_continuous_alias_u (
      .clk(clk), .rst(rst), .start(start));
  fsm_if_nextstate_compare nextstate_compare_u (.clk(clk), .rst(rst), .start(start));
  fsm_if_reversed_compare reversed_compare_u (.clk(clk), .rst(rst));
  fsm_if_duplicate_alias duplicate_alias_u (.clk(clk), .rst(rst), .start(start));
  fsm_if_case_priority case_priority_u (.clk(clk), .rst(rst));

  initial begin
    rst = 1'b1;
    start = 1'b0;
    choose = 1'b0;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) begin
      choose <= 1'b1;
      start <= 1'b0;
    end
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
