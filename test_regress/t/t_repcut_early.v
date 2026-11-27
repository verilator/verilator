// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic reset,
    input logic en,
    input logic force_b,
    input logic [7:0] x,
    input logic [7:0] y,
    output logic [7:0] a,
    output logic [7:0] b,
    output logic [7:0] observation,
    output logic [7:0] repeated
);
  wire [7:0] shared_sum = x + y;
  assign observation = a ^ b;
  assign repeated = {4{x[1:0]}};

  // A transitive clock copy across a module boundary must resolve to clk.
  wire first_clock_alias;
  wire second_clock_alias;
  RepCutClockBuffer buffer1 (.in(clk), .out(first_clock_alias));
  RepCutClockBuffer buffer2 (.in(first_clock_alias), .out(second_clock_alias));

  always @(posedge second_clock_alias) begin
    if (reset) begin
      a <= 0;
    end else begin
      if (en) a <= shared_sum ^ b;
    end
  end

  always @(posedge clk) begin
    if (reset) begin
      b <= 0;
    end else begin
      b <= a;
      if (force_b) b <= shared_sum;
    end
  end
endmodule

module RepCutClockBuffer (input wire in, output wire out);
  assign out = in;
endmodule
