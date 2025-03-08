// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t
  (
   input  wire [ 31:0] foo,
   output reg  [144:0] bar,
   output reg  [144:0] bar2,
   output reg  [144:0] bar3,
   output reg  [144:0] bar4
   );
   // verilator lint_off SELRANGE
   assign bar[159:128] = foo;
   assign bar2[159] = foo[1];
   assign bar3[159 -: 32] = foo;
   assign bar4[128 +: 32] = foo;
endmodule
