// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t(
  clk,
  i0, o0,
  i1, o1
);
  localparam N = 2000;  // Deliberately not multiple of 32

  input clk;
  wire clk;

  // Case 1: concatenations only

  input i0;
  wire [N-1:0] i0;

  output o0;
  wire [N-1:0] o0;

  for (genvar n = 0; n + 31 < N; n += 32) begin
    assign o0[n+ 0 +: 1] = i0[(N-1-n)- 0 -: 1];
    assign o0[n+ 1 +: 1] = i0[(N-1-n)- 1 -: 1];
    assign o0[n+ 2 +: 2] = i0[(N-1-n)- 2 -: 2];
    assign o0[n+ 4 +: 4] = i0[(N-1-n)- 4 -: 4];
    assign o0[n+ 8 +: 8] = i0[(N-1-n)- 8 -: 8];
    assign o0[n+16 +: 8] = i0[(N-1-n)-16 -: 8];
    assign o0[n+24 +: 4] = i0[(N-1-n)-24 -: 4];
    assign o0[n+28 +: 2] = i0[(N-1-n)-28 -: 2];
    assign o0[n+30 +: 1] = i0[(N-1-n)-30 -: 1];
    assign o0[n+31 +: 1] = i0[(N-1-n)-31 -: 1];
  end

  for (genvar n = N / 32 * 32; n < N; ++n) begin
    assign o0[n] = i0[N-1-n];
  end

  // Case 2: mixed concatenations and zero extension

  input i1;
  logic [N-1:0] i1;

  output o1;
  logic [N-1:0] o1;

  always @(posedge clk) begin
    o1 = N'({i1[0 +: N/4], (N/2 - 128)'(i1[N/2 +: N/8]), 128'({i1[0 +: 10], 22'(i1[10 +: 10])})});
  end

endmodule
