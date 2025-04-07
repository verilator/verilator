// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Not super-sensical to have checker without module, but useful for --lint-only

checker check_equal (bit clk, int a, int b);
  assert property (@(posedge clk) a == b);
endchecker
