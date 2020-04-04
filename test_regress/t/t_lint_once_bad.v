// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Check that we report warnings only once on parameterized modules
// Also check that we don't suppress warnings on the same line

module t ();
   sub #(.A(1)) sub1();
   sub #(.A(2)) sub2();
   sub #(.A(3)) sub3();
endmodule

module sub;
   parameter A = 0;

   reg [A:0] unus1;    reg [A:0] unus2;
endmodule
