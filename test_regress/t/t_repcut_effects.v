// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic enable,
    input logic bad,
    input logic done,
    input logic [14:0] data,
    input logic [31:0] fd,
    output logic [14:0] q,
    output logic [14:0] result,
    output logic [63:0] edge_time
);
  timeunit 1ns;
  timeprecision 1ns;
  wire [30:0] effect_seed = {16'b0, data} ^ 31'h4719235;
  for (genvar i = 0; i < 16; i++) begin : effect_chain
    wire [30:0] value;
    if (i == 0) begin
      assign value = (effect_seed << 1) ^ (effect_seed + 31'(data));
    end else begin
      assign value = (effect_chain[i-1].value << 1)
                   ^ (effect_chain[i-1].value + 31'(data) + 31'(i));
    end
  end
`ifdef REPCUT_EFFECT_MULTI
  always @(negedge clk) begin
    if (enable) $display("EFFECT N %0d %0d", effect_chain[15].value, q);
  end
`endif
  assign result = q ^ data;
  always @(posedge clk) begin
    edge_time <= $time;
    q <= data;
    if (enable) begin
      $display("EFFECT A %0d %0d", data, q);
      if (data[0]) $display("EFFECT B %0d", q + 15'd1);
      $fwrite(fd, "EFFECT F %0d\n", q);
      if (effect_chain[15].value[2]) $display("EFFECT C %0d", effect_chain[15].value);
`ifdef REPCUT_EFFECT_FALLBACK
      $display("EFFECT L %0d",
               (effect_chain[15].value / (31'(data) | 31'd1))
               ^ (effect_chain[15].value / (31'(data) | 31'd3))
               ^ (effect_chain[15].value / (31'(data) | 31'd5))
               ^ (effect_chain[15].value / (31'(data) | 31'd9))
               ^ (effect_chain[15].value / (31'(data) | 31'd17))
               ^ (effect_chain[15].value / (31'(data) | 31'd33))
               ^ (effect_chain[15].value / (31'(data) | 31'd65))
               ^ (effect_chain[15].value / (31'(data) | 31'd129)));
`endif
    end
    assert (!bad) else $error("EXPECTED ASSERTION FAILURE %0d", q);
    if (done) $finish;
  end
endmodule
