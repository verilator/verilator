// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Check that lint_off doesn't propagate from include, for post-preprocessor warnings

`include "t_lint_warn_incfile2_bad_b.vh"

module t;
   sub sub();
   int warn_t = 64'h1;  // Not suppressed - should warn
endmodule
