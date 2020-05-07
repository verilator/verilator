// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Make sure type errors aren't suppressable
// verilator lint_off WIDTH

module t(ref int bad_primary_ref
         /*AUTOARG*/);
endmodule
