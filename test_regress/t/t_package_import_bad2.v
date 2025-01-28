// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package Pkg1;
endpackage

package Pkg10;
   // verilator lint_off PKGNODECL
   import Pkg1b::*;  // BAD - typo in package name
endpackage

module t (/*AUTOARG*/);
endmodule
