// DESCRIPTION: Verilator: FSM coverage supports wide sparse state values
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk
);

  typedef enum logic [39:0] {
    E_S0_IDLE = 40'h0000_0000_01,
    E_S1_BUSY = 40'h8000_0000_02,
    E_S2_DONE = 40'hffff_0000_03
  } enum_state_t;

  localparam logic [47:0] L_S0_IDLE = 48'h0000_0000_0001;
  localparam logic [47:0] L_S1_BUSY = 48'h8000_0000_0002;
  localparam logic [47:0] L_S2_DONE = 48'hffff_0000_0003;

  enum_state_t enum_state  /*verilator fsm_reset_arc*/;
  logic rst;
  logic start;
  integer cyc;
  logic [47:0] param_state_q;
  logic [47:0] param_state_d;

  initial begin
    rst = 1'b1;
    start = 1'b0;
    cyc = 0;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) rst <= 1'b0;
    if (cyc == 2) start <= 1'b1;
    if (cyc == 3) start <= 1'b0;
    if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      enum_state <= E_S0_IDLE;
    end
    else begin
      case (enum_state)
        E_S0_IDLE: enum_state <= start ? E_S1_BUSY : E_S0_IDLE;
        E_S1_BUSY: enum_state <= E_S2_DONE;
        default: enum_state <= E_S0_IDLE;
      endcase
    end
  end

  always_comb begin
    param_state_d = param_state_q;
    if (param_state_q == L_S0_IDLE) begin
      param_state_d = start ? L_S1_BUSY : L_S0_IDLE;
    end
    else if (param_state_q == L_S1_BUSY) begin
      param_state_d = L_S2_DONE;
    end
    else if (param_state_q == L_S2_DONE) begin
      param_state_d = L_S0_IDLE;
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      param_state_q <= L_S0_IDLE;
    end
    else begin
      param_state_q <= param_state_d;
    end
  end

endmodule
