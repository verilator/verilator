// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Negative test: a parameterized class :: ref to a member that does not exist
// in a parameter expression should produce a clean error, not crash.

class C #(parameter int a = 0);
  localparam int b = a;
endclass

typedef C#(0) inst;

module t;
  localparam int LP_BAD = inst::nonexistent;
endmodule
