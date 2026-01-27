// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package Pkg1;
endpackage

package Pkg10;
   // verilator lint_off PKGNODECL
   export Pkg1b::*;  // BAD - typo in package name
endpackage

module t;
endmodule
