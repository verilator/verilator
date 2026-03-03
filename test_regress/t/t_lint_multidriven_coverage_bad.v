// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input logic a,
  input logic b,
  output logic [1:0] y
);

  logic [1:0] w;

  assign w[0] = a;  // <--- Warning
  assign w[0] = b;  // <--- Warning
  assign w[1] = 1'b0;

  assign y = w;

endmodule
