// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input x,
    input y,
    output z
);

  logic t2  /* verilator public */;
  logic t3;

  sub u_sub (
      x,
      y,
      t3
  );

  assign t2 = t3 | x;
  assign z = t2;

endmodule

module sub (
    input a  /* verilator forceable */ /* verilator public_flat */,
    input b,
    output c
);

  logic t1;

  assign t1 = a & b;
  assign c = t1;

endmodule
