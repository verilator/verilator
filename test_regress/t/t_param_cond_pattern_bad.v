// DESCRIPTION: Verilator: Verilog Test module
//
// Error for a parameter override that uses ?: to pick an assignment pattern,
// whose condition isn't constant.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

module m #(
    parameter int N = 1,
    parameter int V[N] = '{default: 0}
) ();
endmodule

module t;
  int x;
  m #(.N(2), .V(x > 0 ? '{1, 2} : '{3, 4})) i_var ();  // Not a constant
endmodule
