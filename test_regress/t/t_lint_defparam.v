// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   sub sub ();
   defparam sub.P = 2;

endmodule

module sub;
   parameter P = 6;
endmodule
