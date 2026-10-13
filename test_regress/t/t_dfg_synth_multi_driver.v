// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t #(
    parameter int N = 40000
) (
    input logic [31:0] a,
    output logic [31:0] y
);
  // Allow multiple drivers to the same var to lower number of entries in V3Undriven
  // verilator lint_off MULTIDRIVEN
  logic [31:0] x;
  assign y = x;
  generate
    for (genvar i = 0; i < N; ++i) begin
      always_comb x = a + i;
    end
  endgenerate
  // verilator lint_on MULTIDRIVEN
endmodule
