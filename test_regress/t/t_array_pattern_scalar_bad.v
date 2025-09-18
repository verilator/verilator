// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  bit bad = '{1'b1};  // <--- BAD: Can't assign pattern to scalar

  initial $stop;
endmodule
