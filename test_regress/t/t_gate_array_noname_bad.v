// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 28.3.5: An array of gate instances requires an instance name

module t;
  wire [3:0] a, b, o;
  and [3:0] (o, a, b);  // <--- BAD: range without instance name
endmodule
