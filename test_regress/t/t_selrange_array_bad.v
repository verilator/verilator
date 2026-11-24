// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic [3:0][3:0] i1,
    input logic [1:0][7:0] i2,
    input logic [3:0][0:0] i3,
    input logic [3:0] a,
    output logic [3:0] o1,
    output logic [7:0] o2,
    output logic [3:0] o3,
    output logic o4,
    output logic [3:0] o5,
    output logic o6,
    output logic [7:0] o7
);

  logic [3:0][3:0] w1;

  assign o1 = i1[0];  // No warning
  assign o2 = i2[1];  // No warning
  assign o3 = i1[3];  // No warning
  assign o4 = i1[1][2];  // No warning
  assign o5 = i1[4];  // <--- Warning
  assign o6 = i3[4];  // <--- Warning
  assign o7 = i1[5:4];  // <--- Warning

  always_comb w1[4] = a;  // <--- Warning

endmodule
