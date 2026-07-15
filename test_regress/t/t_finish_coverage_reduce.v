// DESCRIPTION: Verilator: Finish-capable calls are not cloned by expression coverage
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic [3:0] in,
    output logic out
);
  function automatic logic [3:0] maybe_finish(input logic [3:0] value);
    if (&value) $finish;
    return value;
  endfunction

  assign out = &maybe_finish(in);
endmodule
