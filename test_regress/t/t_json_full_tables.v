// DESCRIPTION: Verilator: Complete JSON array initializer tables
//
// This file ONLY is placed under the Creative Commons Public Domain, for any use,
// without warranty, 2026 by Verilator Authors. SPDX-License-Identifier: CC0-1.0

module t (
    input logic [3:0] index,
    output int value
);
  const int values[10] = '{11, 23, 37, 41, 53, 67, 79, 83, 97, 101};
  assign value = values[index];
endmodule
