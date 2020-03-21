// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   parameter integer FOO2 = 32'd-6;  // Minus doesn't go here
   parameter integer FOO3 = 32'd;
   parameter integer FOO4 = 32'h;

endmodule
