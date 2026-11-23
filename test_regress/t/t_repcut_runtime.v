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
    output logic [7:0] controlled,
    output logic [7:0] clock_data,
    output logic [7:0] constant_data,
    output logic [7:0] repeated
);
  wire [7:0] sum = x + y;
  wire [7:0] final_probe = a ^ b;
  assign observation = a ^ b;
  always_comb begin
    if (x[0]) controlled = a;
    else controlled = b;
  end
  assign clock_data = clk ? a : b;
  assign constant_data = 8'h5a;
  assign repeated = {4{x[1:0]}};
  initial begin
    a = 8'h13;
    b = 8'h29;
    $display("RepCut initial ran");
  end
`ifdef REPCUT_NEGEDGE
  always @(negedge clk) begin
`else
  always @(posedge clk) begin
`endif
    if (reset) begin
      a <= 0;
      b <= 0;
    end else begin
      if (en) a <= sum ^ b;
      b <= a;
      if (force_b) b <= sum;
    end
  end
  final begin
    if (final_probe !== (a ^ b)) $stop;
    $display("RepCut final ran");
  end
endmodule
