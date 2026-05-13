// DESCRIPTION: Verilator: FSM coverage for macro/primitive state register wrappers
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module my_fsm_flop #(
    parameter int Width = 1,
    parameter logic [Width-1:0] ResetValue = '0
) (
    input logic clk_i,
    input logic rst_ni,
    input logic [Width-1:0] state_i,
    output logic [Width-1:0] state_o
);
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) state_o <= ResetValue;
    else state_o <= state_i;
  end
endmodule

module prim_flop #(
    parameter int Width = 1,
    parameter logic [Width-1:0] ResetValue = '0
) (
    input logic clk_i,
    input logic rst_ni,
    input logic [Width-1:0] d_i,
    output logic [Width-1:0] q_o
);
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) q_o <= ResetValue;
    else q_o <= d_i;
  end
endmodule

module prim_sparse_fsm_flop #(
    parameter int Width = 1,
    parameter logic [Width-1:0] ResetValue = '0
) (
    input logic clk_i,
    input logic rst_ni,
    input logic [Width-1:0] state_i,
    output logic [Width-1:0] state_o
);
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) state_o <= ResetValue;
    else state_o <= state_i;
  end
endmodule

module odd_fsm_flop #(
    parameter int Width = 1,
    parameter logic [Width-1:0] ResetValue = '0
) (
    input logic clk,
    input logic rst_n,
    input logic [Width-1:0] din,
    output logic [Width-1:0] dout
);
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) dout <= ResetValue;
    else dout <= din;
  end
endmodule

module ambiguous_fsm_flop (
    input logic clk_i,
    input logic rst_ni,
    input logic [1:0] state_i,
    input logic [1:0] d_i,
    output logic [1:0] state_o
);
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) state_o <= 2'd0;
    else state_o <= state_i ^ d_i;
  end
endmodule

module fsm_auto (
    input logic clk,
    input logic rst_n,
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
    unique case (state_q)
      S0: state_d = start ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  my_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_state_regs (
    .clk_i(clk),
    .rst_ni(rst_n),
    .state_i(state_d),
    .state_o(state_q)
  );
endmodule

module fsm_noargs_hint (
    input logic clk,
    input logic rst_n,
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
    unique case (state_q)
      S0: state_d = start ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  my_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_state_regs (
    .clk_i(clk),
    .rst_ni(rst_n),
    .state_i(state_d),
    .state_o(state_q)
  ) /*verilator fsm_state_macro*/;
endmodule

module fsm_prim (
    input logic clk,
    input logic rst_n,
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
    unique case (state_q)
      S0: state_d = start ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  prim_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_state_regs (
    .clk_i(clk),
    .rst_ni(rst_n),
    .d_i(state_d),
    .q_o(state_q)
  );
endmodule

module fsm_sparse_prim (
    input logic clk,
    input logic rst_n,
    input logic start
);
  typedef enum logic [5:0] {
    S0 = 6'b00_0001,
    S1 = 6'b10_0100,
    S2 = 6'b11_0010
  } state_t;

  state_t state_q;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    unique case (state_q)
      S0: state_d = start ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  prim_sparse_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_state_regs (
    .clk_i(clk),
    .rst_ni(rst_n),
    .state_i(state_d),
    .state_o(state_q)
  );
endmodule

module fsm_ifchain (
    input logic clk,
    input logic rst_n,
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
    if (state_q == S0) begin
      state_d = start ? S1 : S0;
    end
    else if (state_q == S1) begin
      state_d = S2;
    end
    else begin
      state_d = S0;
    end
  end

  my_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_state_regs (
    .clk_i(clk),
    .rst_ni(rst_n),
    .state_i(state_d),
    .state_o(state_q)
  );
endmodule

module fsm_wide_sparse (
    input logic clk,
    input logic rst_n,
    input logic start
);
  typedef enum logic [39:0] {
    S0 = 40'h0000_0000_01,
    S1 = 40'h8000_0000_02,
    S2 = 40'hffff_0000_03
  } state_t;

  state_t state_q;
  state_t state_d;

  always_comb begin
    state_d = state_q;
    unique case (state_q)
      S0: state_d = start ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  my_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_state_regs (
    .clk_i(clk),
    .rst_ni(rst_n),
    .state_i(state_d),
    .state_o(state_q)
  );
endmodule

module fsm_annotated (
    input logic clk,
    input logic rst_n,
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
    unique case (state_q)
      S0: state_d = start ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  odd_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_state_regs (
    .clk(clk),
    .rst_n(rst_n),
    .din(state_d),
    .dout(state_q)
  ) /*verilator fsm_state_macro d=din q=dout clk=clk rst=rst_n rstval=ResetValue*/;
endmodule

module fsm_non_simple (
    input logic clk,
    input logic rst_n,
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
    unique case (state_q)
      S0: state_d = start ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  my_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_state_regs (
    .clk_i(clk),
    .rst_ni(rst_n),
    .state_i(state_d[1:0]),
    .state_o(state_q)
  );
endmodule

module fsm_ambiguous (
    input logic clk,
    input logic rst_n,
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
    unique case (state_q)
      S0: state_d = start ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  ambiguous_fsm_flop u_state_regs (
    .clk_i(clk),
    .rst_ni(rst_n),
    .state_i(state_d),
    .d_i(state_d),
    .state_o(state_q)
  );
endmodule

module fsm_ignored (
    input logic clk,
    input logic rst_n,
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
    unique case (state_q)
      S0: state_d = start ? S1 : S0;
      S1: state_d = S2;
      default: state_d = S0;
    endcase
  end

  odd_fsm_flop #(
    .Width($bits(state_t)),
    .ResetValue(S0)
  ) u_state_regs (
    .clk(clk),
    .rst_n(rst_n),
    .din(state_d),
    .dout(state_q)
  );
endmodule

module t (
    input logic clk
);
  logic rst_n;
  logic start;
  integer cyc;

  initial begin
    rst_n = 1'b0;
    start = 1'b0;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst_n <= 1'b1;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) start <= 1'b0;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  fsm_auto auto_u (.clk(clk), .rst_n(rst_n), .start(start));
  fsm_noargs_hint noargs_u (.clk(clk), .rst_n(rst_n), .start(start));
  fsm_prim prim_u (.clk(clk), .rst_n(rst_n), .start(start));
  fsm_sparse_prim sparse_prim_u (.clk(clk), .rst_n(rst_n), .start(start));
  fsm_ifchain ifchain_u (.clk(clk), .rst_n(rst_n), .start(start));
  fsm_wide_sparse wide_sparse_u (.clk(clk), .rst_n(rst_n), .start(start));
  fsm_annotated annotated_u (.clk(clk), .rst_n(rst_n), .start(start));
  fsm_non_simple non_simple_u (.clk(clk), .rst_n(rst_n), .start(start));
  fsm_ambiguous ambiguous_u (.clk(clk), .rst_n(rst_n), .start(start));
  fsm_ignored ignored_u (.clk(clk), .rst_n(rst_n), .start(start));
endmodule
