// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifdef verilator
  `verilator_config
    lint_off -rule DECLFILENAME
    // Test filename matches are in directive parse order
    lint_off -rule UNUSED -file "*/t_*"  // Sorts before t_vlt_*
    lint_off -rule UNUSED -file "*/t_vlt_warn*"  // Sorts after t_vlt_*
    lint_on -rule UNUSED -file "*/t_vlt_*"
    lint_off -rule UNUSED -file "*/t_vlt_warn*" -lines 21-22
  `verilog
`endif


module t;
  reg unuse_warn_var_line20;  // Unused warning - must be line 20 (on)
  reg unuse_warn2_var_line21;  // Unused warning - must be line 21 (off)
  reg unuse_warn3_var_line22;  // Unused warning - must be line 22 (off)
endmodule
