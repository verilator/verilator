// DESCRIPTION: Verilator: FSM coverage keeps grouped accepted policy-style forms
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Group accepted policy-driven forms that should stay inferred, even though
// they exercise different coverage attributes or non-enum state policies.

module fsm_style_incl (
    input logic clk,
    input logic rst,
    input logic start
);
  typedef enum logic [1:0] {
    S0 = 2'd0,
    S1 = 2'd1,
    S2 = 2'd2,
    S3 = 2'd3
  } state_t;

  state_t state  /*verilator fsm_arc_include_cond*/;

  always_ff @(posedge clk) begin
    if (rst) begin
      state <= S0;
    end
    else begin
      case (state)
        S0:
        if (start) state <= S1;
        else state <= S2;
        S1: state <= S3;
        default: state <= S0;
      endcase
    end
  end
endmodule

module fsm_default_incl_ok (
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
    case (state_q)
      S0: state_d = start ? S1 : S2;
      default: state_d = S0;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) state_q <= S0;
    else state_q <= state_d;
  end
endmodule

module fsm_forced_ok (
    input logic clk,
    input logic rst
);
  logic [1:0] state  /*verilator fsm_state*/;

  always_ff @(posedge clk) begin
    if (rst) begin
      state <= 2'd0;
    end
    else begin
      case (state)
        2'd0: state <= 2'd1;
        2'd1: state <= 2'd2;
        default: state <= 2'd0;
      endcase
    end
  end
endmodule

module t (
    input logic clk
);
  integer cyc;
  logic rst;
  logic start;

  fsm_style_incl style_u (
      .clk(clk),
      .rst(rst),
      .start(start)
  );
  fsm_default_incl_ok default_incl_u (
      .clk(clk),
      .rst(rst),
      .start(start)
  );
  fsm_forced_ok forced_u (
      .clk(clk),
      .rst(rst)
  );

  initial begin
    cyc = 0;
    rst = 1'b1;
    start = 1'b0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) start <= 1'b0;
    if (cyc == 6) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
