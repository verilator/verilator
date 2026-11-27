// DESCRIPTION: Verilator: Trace activity across RepCut publication joins
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ns
module t #(
  parameter STATE_WORDS = 1
) (
  input logic clk_a, clk_b, reset,
  input logic [3:0] en,
  input logic [31:0] data,
  output wire [64*32*STATE_WORDS-1:0] result,
  output wire [31:0] structured
);
  typedef struct packed {
    logic [16:0] high;
    logic [14:0] low;
  } word_t;
  word_t structured_state;
  always_ff @(posedge clk_a)
    if (reset) structured_state <= '0;
    else if (en[0]) structured_state <= word_t'(structured_state + data + 32'd5);
  assign structured = structured_state;

  // Enough traced state to retain fine-grained activity flags. A small
  // fixture can turn into unconditional tracing and hide missing setters.
  for (genvar g = 0; g < 64; ++g) begin : bank
    logic [32*STATE_WORDS-1:0] q;
    if (g % 2 == 0) begin : a
      always_ff @(posedge clk_a)
        if (reset) q <= (32*STATE_WORDS)'(g);
        else if (en[g%4]) q <= q + (32*STATE_WORDS)'(data) + (32*STATE_WORDS)'(g+1);
    end else begin : b
      always_ff @(posedge clk_b)
        if (reset) q <= (32*STATE_WORDS)'(g);
        else if (en[g%4]) q <= q + (32*STATE_WORDS)'(data) + (32*STATE_WORDS)'(g+1);
    end
    assign result[32*STATE_WORDS*g+:32*STATE_WORDS] = q;
  end
endmodule
