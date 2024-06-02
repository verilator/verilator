// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   wire foo;
   wire bar;

   sub sub (.*, .*);

   sub sub (foo, .*);

   sub sub (foo, .bar);

endmodule

module sub (input foo, input bar);
endmodule
