// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   subok subok (.a(1'b1), .b(1'b0));
   sub sub (.a(1'b1), .b(1'b0));
endmodule

module subok (input a,b);
endmodule

module sub (a);
   input a, b;
endmodule
