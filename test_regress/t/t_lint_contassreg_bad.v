// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0


module t (
    r,
    rr,
    ri,
    wr
);

  output r;

  reg r;

  assign r = 1'b0;  // Bad

  reg rr;
  output rr;
  output integer ri;
  wire wr;
  output wr;

  assign rr = 1'b0;  // Bad
  assign ri = 0;  // Bad
  assign wr = 1'b0;

  sub sub (
      .a(),
      .b(),
      .c(),
      .d(),
      .e(),
      .f()
  );
endmodule

module sub (
    output reg a,
    b,
    output c,
    output signed [1:0] d,
    output wire e,
    output integer f
);
  assign a = 1'b0;  // Bad
  assign b = 1'b0;  // Bad
  assign c = 1'b0;
  assign d = 2'b0;
  assign e = 1'b0;
  assign f = 0;  // Bad
endmodule
