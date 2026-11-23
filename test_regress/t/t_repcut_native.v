// DESCRIPTION: Verilator: RepCut kernels with native event scheduling
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ns
module t (
  input bit clk_a, clk_b, reset_n, gate,
  input logic [14:0] x,
  output logic [14:0] a, b, gated, divided, mem_out,
  output logic divider
);
  logic [14:0] memory [0:3];
`ifdef NATIVE_FEATURES
  import "DPI-C" context function int unsigned repcut_native_context(input int unsigned value);
  export "DPI-C" function repcut_native_read;
  int unsigned queue_data[$];
  string text_value;
  int unsigned behavioral, discarded;
  int unsigned loop_value, real_value;
  bit timed_clock = 0;
  logic [14:0] timed_state;
  int unsigned context_result;
  function int unsigned repcut_native_read();
    return int'(a) ^ behavioral;
  endfunction
  always #3 timed_clock = !timed_clock;
  always @(posedge clk_b) begin
    if (!reset_n) context_result <= 0;
    else context_result <= repcut_native_context(int'(x));
  end
  always @(posedge clk_b) begin
    if (!reset_n) begin
      queue_data.delete();
      text_value = "reset";
      behavioral <= 0;
    end else begin
      queue_data.push_back(int'(x));
      if (queue_data.size() > 4) discarded = queue_data.pop_front();
      text_value = $sformatf("value=%0x", x);
      behavioral <= queue_data.sum() ^ int'(text_value.len());
    end
  end
  always_comb begin
    loop_value = 0;
    for (int i = 0; i < int'(x[2:0]); ++i) loop_value = (loop_value << 1) ^ int'(x);
  end
  always_comb real_value = int'(real'(x) * 1.25);
  always @(posedge timed_clock or negedge reset_n) begin
    if (!reset_n) timed_state <= 0;
    else timed_state <= a ^ 15'(behavioral);
  end
  wire [14:0] mix = (a + x) ^ (b << 1) ^ 15'(behavioral ^ loop_value ^ real_value ^ context_result) ^ timed_state;
`elsif NATIVE_CYCLE
  wire [14:0] feedback = x | (feedback << 1);
  wire [14:0] mix = (a + x) ^ (b << 1) ^ feedback;
`else
  wire [14:0] mix = (a + x) ^ (b << 1);
`endif
  wire gated_clock = clk_a & gate;
  assign mem_out = memory[x[1:0]];
  always @(posedge clk_a or negedge reset_n) begin
    if (!reset_n) begin
      a <= 0;
      divider <= 0;
    end else begin
      a <= mix;
      divider <= !divider;
    end
  end
  always @(posedge clk_b or negedge reset_n) begin
    if (!reset_n) b <= 0;
    else b <= (a ^ x) + 15'h321;
  end
  always @(posedge gated_clock or negedge reset_n) begin
    if (!reset_n) gated <= 0;
    else gated <= a + b;
  end
  always @(posedge divider or negedge reset_n) begin
    if (!reset_n) divided <= 0;
    else divided <= a ^ b;
  end
  always @(posedge clk_b) begin
    memory[x[1:0]] <= mix;
    if (gate) memory[x[1:0]] <= a;
  end
endmodule
