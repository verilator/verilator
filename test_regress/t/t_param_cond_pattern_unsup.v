// DESCRIPTION: Verilator: Verilog Test module
//
// A parameter override that uses ?: to pick between an assignment pattern and
// something else is still unsupported. A ?: of patterns where nothing gives
// them a type gets the same error. A condition without a known value, such as
// x or z, is also unsupported.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

typedef int two_t[2];

module m #(
    parameter int V[2] = '{0, 0}
) ();
endmodule

module t;
  localparam int ARR[2] = '{7, 8};
  m #(.V(1 ? '{1, 2} : ARR)) i ();
  m #(.V(two_t'{$bits(1 ? '{1, 2} : '{3, 4}), 0})) i_bits ();
  m #(.V(1'bx ? '{1, 2} : '{3, 4})) i_x ();
  m #(.V(1'bz ? '{1, 2} : '{3, 4})) i_z ();
  m #(.V((1'bx ? 1'b1 : 1'b0) ? '{1, 2} : '{3, 4})) i_xcond ();
endmodule
