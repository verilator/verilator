// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

`define DUP a
`define DUP b_bad

// verilator lint_off REDEFMACRO
`define DUP c_nowarn
// verilator lint_on REDEFMACRO
`define DUP d_bad
// verilator lint_save
// verilator lint_off REDEFMACRO
`define DUP e_nowarn
// verilator lint_restore
`define DUP f_bad

/* verilator lint_off REDEFMACRO */
`define DUP j_nowarn
/* verilator lint_on REDEFMACRO */
`define DUP k_bad
/* verilator lint_save */
/* verilator lint_off REDEFMACRO */
`define DUP l_nowarn
/* verilator lint_restore */
`define DUP m_bad

endmodule
