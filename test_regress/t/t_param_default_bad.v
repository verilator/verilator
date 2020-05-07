// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module m #(parameter int Foo);
endmodule

module t (/*AUTOARG*/);

   m foo();

endmodule
