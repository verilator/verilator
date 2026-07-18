// DESCRIPTION: Verilator: FSM coverage ignores unrelated datapath comparisons
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module datapath_only #(
    parameter logic [15:0] MASK = 16'hff00,
    parameter logic [15:0] MATCH = 16'h1200
) (
    input logic [6:0] a,
    input logic b,
    input logic [15:0] data,
    output logic concat_hit,
    output logic masked_hit
);
  assign concat_hit = ({a, b} == 8'h00);
  assign masked_hit = (data & MASK) == MATCH;
endmodule

module t #(
    parameter logic [15:0] MASK = 16'hff00,
    parameter logic [15:0] MATCH = 16'h1200
) (
    input logic clk,
    input logic rst,
    input logic go,
    input logic [6:0] a,
    input logic b,
    input logic [15:0] data,
    output logic busy,
    output logic hit,
    output logic concat_hit,
    output logic masked_hit
);
  typedef enum logic [1:0] {
    IDLE,
    RUN,
    DONE
  } state_t;
  state_t state;

  always_ff @(posedge clk) begin
    if (rst) begin
      state <= IDLE;
    end
    else begin
      case (state)
        IDLE: if (go) state <= RUN;
        RUN: state <= DONE;
        DONE: state <= IDLE;
        default: state <= IDLE;
      endcase
    end
  end

  assign busy = (state != IDLE);
  assign hit = (data & MASK) == MATCH;

  datapath_only datapath_only_u (
      .a(a),
      .b(b),
      .data(data),
      .concat_hit(concat_hit),
      .masked_hit(masked_hit)
  );
endmodule
