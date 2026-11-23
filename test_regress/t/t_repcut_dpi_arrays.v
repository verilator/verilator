// DESCRIPTION: Verilator: Native RepCut DPI array input capture
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input bit clk,
  input bit reset,
  input bit enable,
  input logic [94:0] x,
  output logic [94:0] q,
  output int unsigned previous,
  output int unsigned observed,
  output logic [63:0] rtl
);
  typedef byte unsigned lane_t;
  lane_t descending [7:3];
  lane_t ascending [2:6];
  lane_t reply [3:7];
  chandle handle;
  bit initialized = 0;
  int unsigned result;
  logic [94:0] scratch;

  import "DPI-C" function chandle repcut_array_init();
  import "DPI-C" function int unsigned repcut_array_tick(
    input chandle handle, input lane_t descending [], input lane_t ascending [],
    output lane_t reply []);

  for (genvar i = 0; i < 5; i++) begin
`ifdef PARTIAL_ARRAY
    if (i == 2) begin
      initial descending[3+i] = 8'hc7;
      always @(negedge clk) begin
        if (reset) descending[3+i] = 8'hc7;
        else if (enable) descending[3+i] = descending[3+i] + 8'h13;
      end
    end else begin
      always @* descending[3+i] = x[8*i +: 8] ^ 8'(3*i+1);
    end
`else
    assign descending[3+i] = x[8*i +: 8] ^ 8'(3*i+1);
`endif
    assign ascending[2+i] = x[8*i+40 +: 8] + 8'(5*i+7);
  end

  always @(posedge clk) begin
    if (reset) begin
      q <= 0;
      previous <= 0;
      observed <= 0;
    end else if (enable) begin
      if (!initialized) begin
        handle = repcut_array_init();
        initialized = 1;
      end
      result = repcut_array_tick(handle, descending, ascending, reply);
      scratch = {31'(result), x[63:0]};
      scratch[17 +: 17] = {reply[3], reply[5], result[0]};
      scratch[80 +: 15] = {7'(reply[4]), reply[7]};
      q <= scratch;
      previous <= q[31:0];
      observed <= result;
    end
  end
  always @(posedge clk) begin
    if (reset) rtl <= 0;
    else rtl <= x[63:0] ^ q[63:0];
  end
endmodule
