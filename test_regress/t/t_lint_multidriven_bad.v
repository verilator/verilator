// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
  // Outputs
  out, out2,
  // Inputs
  clk, d0, d1
  );

  input clk;
  input [7:0] d0;
  input [7:0] d1;
  output reg [31:0] out;
  output reg [15:0] out2;

  reg [7:0] q;

  always_ff @(posedge clk) begin
    q <= d0;  // <--- Warning
  end
  always_ff @(negedge clk) begin
    q <= d1;  // <--- Warning
  end
  assign out = {4{q}};

  always_ff @(posedge clk) begin
    out2[7:0] <= d0;  // No warning, different bits
  end
  always_ff @(negedge clk) begin
    out2[15:8] <= d0;  // No warning, different bits
  end

endmodule
