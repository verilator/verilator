// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// --output-split-cfuncs chops the reconstruct body into sub-functions; the epoch memo
// lives in the entry function and must survive that.
module t (
  input logic clk,
  input logic [7:0] a,
  input logic [7:0] b,
  output logic [7:0] observe
);

  logic [7:0] m1;
  logic [7:0] m2;
  logic [7:0] m3;
  logic [7:0] m4;

  always_comb begin
    m1 = a ^ 8'h5a;
    m2 = m1 + b;
    m3 = m2 ^ 8'h3c;
    m4 = m3 + 8'h11;
  end

  logic [7:0] flopped;
  always_ff @(posedge clk) flopped <= m4;

  assign observe = flopped;

endmodule
