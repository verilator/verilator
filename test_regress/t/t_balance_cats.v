// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off UNOPTFLAT

module t(i, o);
  localparam N = 2000; // Deliberately not multiple of 32

  input i;
  wire [N-1:0] i;

  output o;
  wire [N-1:0] o;

  for (genvar n = 0 ; n + 31 < N ; n += 32) begin
    assign o[n+ 0 +: 1] = i[(N-1-n)- 0 -: 1];
    assign o[n+ 1 +: 1] = i[(N-1-n)- 1 -: 1];
    assign o[n+ 2 +: 2] = i[(N-1-n)- 2 -: 2];
    assign o[n+ 4 +: 4] = i[(N-1-n)- 4 -: 4];
    assign o[n+ 8 +: 8] = i[(N-1-n)- 8 -: 8];
    assign o[n+16 +: 8] = i[(N-1-n)-16 -: 8];
    assign o[n+24 +: 4] = i[(N-1-n)-24 -: 4];
    assign o[n+28 +: 2] = i[(N-1-n)-28 -: 2];
    assign o[n+30 +: 1] = i[(N-1-n)-30 -: 1];
    assign o[n+31 +: 1] = i[(N-1-n)-31 -: 1];
  end

  for (genvar n = N / 32 * 32; n < N ; ++n) begin
    assign o[n] = i[N-1-n];
  end

endmodule
