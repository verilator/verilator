// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   a a ();
   defparam a.b.W = 3;
endmodule

module a;
   b b();
endmodule

module b;
   parameter W = 0;
endmodule
