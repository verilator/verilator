// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  int array_bad[0];  // <--- Error: Must be positive size
  int array2_bad[-1];  // <--- Error: Must be positive size
  localparam X = 32'bz;
  // verilator lint_off SIMILARNAME
  logic [X:0] x;  // <--- Error: X range
  // verilator lint_on SIMILARNAME
  sub #(1) u_sub ();
endmodule

module sub #(
    parameter SIZE = 0
);
  int ignore[SIZE];
endmodule
