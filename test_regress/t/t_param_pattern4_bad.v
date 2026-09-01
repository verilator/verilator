// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A parameter whose data type depends on a parameter whose own value is circular.  The
// reference is left in place rather than substituted, so the usual circular value check
// reports it instead of the substitution recursing forever.
module dut_circ #(
    parameter int N = N + 1,
    parameter int ARR[N] = '{1, 1}
) (
    output int o
);
  assign o = ARR[0];
endmodule

module t;
  int o_circ;
  dut_circ #(.ARR('{1, 2})) u_circ (.o(o_circ));
endmodule
