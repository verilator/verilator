// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic reset,
    input logic [2:0] mode,
    input logic en,
    input logic select,
    input logic [6:0] a,
    input logic [6:0] b,
    input logic [1:0] rd,
    input logic [1:0] wr,
    input logic signed [94:0] wa,
    input logic signed [94:0] wb,
    output logic [6:0] q,
    output logic [6:0] y,
    output logic [6:0] data,
    output logic signed [94:0] wq,
    output logic [6:0] local_result,
    output logic [6:0] observed_y,
    output logic signed [94:0] wide_result
);
  wire [6:0] shared_sum = a + b;
  wire [6:0] local_term = (a ^ b) + 7'h13;
  assign local_result = (local_term & a) ^ (local_term + b);
  assign observed_y = y ^ q;
  assign wide_result = select ? (wa ^ wb) : (wa & wb);
  logic [6:0] mem [0:2];
  initial begin
    q = 5;
    wq = 0;
    mem[0] = 11;
    mem[1] = 22;
    mem[2] = 33;
  end
  always_comb begin
    y = shared_sum;
    if (|mode) begin
      y = shared_sum ^ a;
      if (en) y = y + b;
      else y = b - a;
    end else begin
      y = select ? a * b : a ^ b;
    end
  end
  always @(posedge clk) begin
    if (reset) wq <= 0;
    else if (en) wq <= (wa >>> 3) + wb;
    if (reset) q <= 0;
    else begin
      if (|mode) begin
        if (en) q <= shared_sum ^ q;
        else q <= q + b;
      end
      // This NBA has priority; every RHS still reads the old state.
      if (select) q <= a;
    end
    if (|mode) begin
      if (en) begin
        mem[wr] <= shared_sum;
        if (select) mem[wr] <= a ^ b;
      end else mem[rd] <= a;
    end
  end
  assign data = (|mode) ? (en ? mem[rd] : b) : a;
endmodule
