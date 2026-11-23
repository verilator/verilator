// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk, reset, enable, select,
    input logic [30:0] data31,
    input logic [63:0] data64,
    input logic signed [94:0] data95,
    input logic [128:0] data129,
    output logic [31:0] observed,
    output logic [31:0] state31, state64, state95, state129,
    output logic [3:0] truncated,
    output logic single_bit
);
  // One missing pure operation must not keep this complete dependency cone
  // outside the partition graph. Branches and wide/signed operands survive.
  wire [31:0] alu_result = select
      ? ($countones(data31) + $countones(data64)) ^ state95
      : ($countones(data95) + $countones(data129)) ^ state31;
  assign observed = alu_result;
  always @(posedge clk) begin
    if (reset) begin
      state31 <= 3;
      state64 <= 5;
      state95 <= 7;
      state129 <= 11;
      truncated <= 0;
      single_bit <= 0;
    end else if (enable) begin
      state31 <= alu_result + state64;
      state64 <= $countones(data64 ^ {32'b0, state31});
      state95 <= $countones(data95) + state129;
      state129 <= $countones(data129) ^ state95;
      truncated <= 4'($countones(data95));
      single_bit <= 1'($countones(data31[0]));
      if (select && data31[1]) state31 <= $countones(data129) + state31;
    end
  end
endmodule
