// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2011 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   sub sub ();
endmodule

module sub #(parameter WIDTH=X, parameter X=WIDTH)
   ();
endmodule
