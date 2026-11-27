// DESCRIPTION: Verilator: RepCut clocked DPI captures must be fresh on each edge
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input bit clk,
  input bit reset,
  input bit enable,
  input bit clk_b,
  input bit gate,
  input bit async_reset,
  input longint unsigned delta,
  output longint unsigned q,
  output logic [62:0] neg_q,
  output logic [62:0] async_q,
  output logic [62:0] cross_q
);
  counter counter(clk, reset, delta, q, neg_q);
  observer observer(clk, enable, q, neg_q);
  wire generated_clock = clk_b & gate;
  always @(posedge generated_clock or posedge async_reset) begin
    if (async_reset) async_q <= 0;
    else async_q <= async_q + delta[62:0] + q[62:0] + 3;
  end
  always @(negedge clk_b) cross_q <= async_q;
  async_observer async_observer(generated_clock, async_reset, async_q);
endmodule

module async_observer (
  input bit generated_clock,
  input bit async_reset,
  input logic [62:0] async_q
);
  import "DPI-C" function void repcut_observe(input int unsigned lane,
                                            input longint unsigned value);
  always @(posedge generated_clock or posedge async_reset)
    repcut_observe(2, {1'b0, async_q});
endmodule

module counter (
  input bit clk,
  input bit reset,
  input longint unsigned delta,
  output longint unsigned q,
  output logic [62:0] neg_q
);
  always @(posedge clk) begin
    if (reset) q <= 0;
    else q <= q + 1;
  end
  always @(negedge clk) begin
    if (reset) neg_q <= 0;
    else neg_q <= neg_q + delta[62:0] + 1;
  end
endmodule

module observer (
  input bit clk,
  input bit enable,
  input longint unsigned q,
  input logic [62:0] neg_q
);
  import "DPI-C" function void repcut_observe(input int unsigned lane,
                                            input longint unsigned value);
  always @(posedge clk) repcut_observe(0, q);
  always @(negedge clk) begin
    if (enable) repcut_observe(1, {1'b0, neg_q});
  end
endmodule
