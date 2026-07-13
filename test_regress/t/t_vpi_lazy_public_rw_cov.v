// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Regression: --vpi-lazy-public-rw + --coverage abort at compile.
module t (
  input logic clk,
  input logic [3:0] a,
  input logic [3:0] b,
  output logic [3:0] o
);
  logic [3:0] cmb;
  assign cmb = a & b;

  logic [3:0] cmb2;
  always_comb cmb2 = cmb ^ a;

  logic [3:0] result;
  always_ff @(posedge clk) result <= cmb2 ^ b;

  assign o = result;
endmodule
