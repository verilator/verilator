// DESCRIPTION: Verilator: Finish propagation selectivity
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0

module t (
  input  logic [7:0] in,
  output logic [7:0] out
);
  function automatic logic [7:0] increment(logic [7:0] value);
    return value + 1'b1;
  endfunction

  always_comb out = increment(in);
endmodule
