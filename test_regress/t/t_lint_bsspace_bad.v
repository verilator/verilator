// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Fake binary character here '', so is treated as binary and
// don't get whitespace violation.

`define FOO   blak \ 
   blak

module t;
endmodule
