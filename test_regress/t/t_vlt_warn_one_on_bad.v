// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifdef verilator
  `verilator_config
    // Issue #4185
    lint_off
    lint_on -rule UNUSEDPARAM
  `verilog
`endif





module t;
  reg unuse_warn_var_line20;  // Unused warning - must be line 20
  reg unuse_warn2_var_line21;  // Unused warning - must be line 21
  reg unuse_warn3_var_line22;  // Unused warning - must be line 22
  reg unuse_warn4_var_line23;  // Unused warning - must be line 23
  localparam unuse_warn5_var_line24 = 0;  // Unused warning - must be line 24 (not suppressed)
  localparam unuse_warn5_var_line25 = 0;  // Unused warning - must be line 25 (not suppressed)

endmodule
