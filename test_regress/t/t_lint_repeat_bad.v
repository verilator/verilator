// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t ();

   sub #(.Z(0)) sub1 ();
   sub #(.Z(1)) sub2 ();
   sub #(.Z(2)) sub3 ();

endmodule

module sub;
   parameter Z = 0;
   wire [1:0] a = 2'b11;
   wire [0:0] b = a;
endmodule
