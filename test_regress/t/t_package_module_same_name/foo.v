// DESCRIPTION: Verilator: Autoloaded module sharing a package name
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module foo (
    input clk,
    output int o
);
  /*verilator no_inline_module*/
  int r = 20;
  always @(posedge clk) r <= r + 1;
  assign o = r;
endmodule
