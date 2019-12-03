// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

module t (/*AUTOARG*/);

   parameter integer FOO2 = 32'd-6;  // Minus doesn't go here
   parameter integer FOO3 = 32'd;
   parameter integer FOO4 = 32'h;

endmodule
