// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module sub (
    i
);
  parameter N = 3;
  input [N : 0] i;  // Note 3:0 conflicts until parameterize
  wire [2:0] i;
endmodule

module t;
  wire [2:0] i;
  sub #(.N(2)) sub (.i);
endmodule
