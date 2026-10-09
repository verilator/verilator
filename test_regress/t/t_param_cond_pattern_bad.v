// DESCRIPTION: Verilator: Verilog Test module
//
// A parameter override that uses ?: to pick between assignment patterns
// needs a constant condition.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

module m #(
    parameter int V[2] = '{0, 0}
) ();
endmodule

module t;
  bit b = 1'b1;
  m #(.V(b ? '{1, 2} : '{3, 4})) i ();
endmodule
