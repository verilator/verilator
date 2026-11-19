// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic [1:0] a,
    input logic [1:0] b,
    input logic [1:0] a2,
    input logic [1:0] b2,
    output logic [1:0] q,
    output logic [1:0] qff,
    output logic [0:0] s,
    output logic [3:0] r
);

  always_comb q[1:0] = a[1:0];  // <--- Warning
  assign q[1:0] = b[1:0];  // <--- Warning

  always_ff @(posedge clk) qff[1:0] <= a[1:0];  // <--- Warning
  assign qff[1:0] = b[1:0];  // <--- Warning

  always_comb s[0] = a[0];  // <--- Warning
  assign s[0] = b[0];  // <--- Warning

  always_comb r[1:0] = a2;  // No warning, different bits
  assign r[3:2] = b2;  // No warning, different bits

endmodule
