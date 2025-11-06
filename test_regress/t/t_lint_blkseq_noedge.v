// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
    lhs,
    o
);
  input wire [7:0] lhs;
  output reg [7:0] o;

  wire [7:0] shifted;

  always @(shifted or lhs) begin
    if (lhs[7]) o = shifted ^ 8'h1b;
    else o = shifted;
  end

  assign shifted = lhs << 1;

endmodule
