// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   parameter integer FOO2 = 32'd-6;  // Minus doesn't go here
   parameter integer FOO3 = 32'd;
   parameter integer FOO4 = 32'h;

   parameter integer FOO5 = 32'b2;
   parameter integer FOO6 = 32'o8;

   // See bug2432, this is questionable, some simulators take this, others do not
   parameter logic [3:0] FOO7 = 1'b1?4'hF:4'h1;  // bug2432 - intentionally no spaces near ?

endmodule
