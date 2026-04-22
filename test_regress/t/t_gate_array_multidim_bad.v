// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Verify multi-dim gate primitive arrays are rejected.

module t;
  wire a, b;
  wire [1:0][1:0] y;
  and g [1:0][1:0] (y, a, b);
endmodule
