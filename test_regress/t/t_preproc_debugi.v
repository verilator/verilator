// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define FOO
`define BAR(aa,bb) aa bb
`FOO
`BAR(aa,bb)
