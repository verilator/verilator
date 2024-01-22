// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module foo(input logic i_clk); /* verilator public_module */
endmodule

// --flatten forces inlining of public module foo.
module top(input logic i_clk);
  foo f(.*);
endmodule
