// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Check that `line `__LINE__ still shows proper warning context

`line `__LINE__ "the_line_file" 1
`line `__LINE__ "the_line_file" 2

module t;
   int warn_t = 64'h1;  // Not suppressed - should warn
endmodule
