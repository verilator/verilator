// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

//bug1587
module t;
   reg a[0];
   reg b;
   reg c;
   initial c = (a != &b);
endmodule
