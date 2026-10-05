// DESCRIPTION: Verilator: Misspelled package suggests the declared package
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package my_pkg;
  localparam int X = 1;
endpackage

module t;
  int y = my_pkgg::X;
endmodule
