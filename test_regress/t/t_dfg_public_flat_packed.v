// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic a,
    input logic b,
    output logic [2:0] result,
    output logic [2:0] partial_out
);
  assign result[0] = a;
  assign result[1] = b;
  assign result[2] = ^result[1:0];

  // verilator lint_off UNOPTFLAT
  logic [2:0] partial;
  assign partial[0] = a;
  assign partial[2] = partial[1] ^ b;
  assign partial_out = partial;
  // verilator lint_on UNOPTFLAT
endmodule
