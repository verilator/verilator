// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifdef verilator
  `verilator_config
    lint_off -rule DECLFILENAME
    // Test overlapping ranges work correctly
    lint_off -rule UNUSED -file "*/t_*" -lines 21-23
    lint_off -rule UNUSED -file "*/t_*" -lines 20-22  // Intentional overlap with above
    lint_off -rule UNUSED -file "*/t_*" -lines 25-99
    lint_on -rule UNUSED -file "*/t_*" -lines 26
  `verilog
`endif


module t;
  reg unuse_warn_var_line20;  // Unused warning - must be line 20
  reg unuse_warn2_var_line21;  // Unused warning - must be line 21
  reg unuse_warn3_var_line22;  // Unused warning - must be line 22
  reg unuse_warn4_var_line23;  // Unused warning - must be line 23
  reg unuse_warn5_var_line24;  // Unused warning - must be line 24 (not suppressed)
  reg unuse_warn5_var_line25;  // Unused warning - must be line 25
  reg unuse_warn5_var_line26;  // Unused warning - must be line 26 (turned on)
  reg unuse_warn5_var_line27;  // Unused warning - must be line 27
endmodule
