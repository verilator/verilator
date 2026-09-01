// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// The array's size parameter has no default and is not overridden either, so this
// instance has no value at all to substitute for it.
module dut #(
    parameter int ARRAY_LEN,
    parameter int ARRAY_PARAM[ARRAY_LEN] = '{1, 1}
) (
    output int o
);
  assign o = ARRAY_PARAM[0];
endmodule

module t;
  int o;
  dut #(.ARRAY_PARAM('{1, 2, 3})) u (.o(o));
endmodule
