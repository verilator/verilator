// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  int i;
  int a[2];
  initial begin
    $dumpvars(1, a[i]);  // Index is not a constant
    $dumpvars(1, i + 1);  // Not a name
    $dumpvars(1, a[i].x);  // Not a name before the dot
    $dumpvars(1, a[i][0]);  // Not a name before the index
  end
endmodule
