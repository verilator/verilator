// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk,
    input [7:0] in,
    output reg [7:0] a,
    output reg [7:0] b,
    output reg [7:0] errors
);

  // Split into one block per variable. The assertion's failure branch has no
  // statement V3Branch treats as unlikely, so its prediction must survive the split.
  always @(posedge clk) begin
    a = in;
    b = ~in;
    assert (in != 8'hff) else errors = errors + 1;
  end

endmodule
