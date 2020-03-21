// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module a_top;
   a a ();
   initial begin
      $write("Bad top modules\n");
      $stop;
   end
endmodule

module a;
   b b ();
   c c ();
   d d ();
endmodule

module b;
endmodule

module c;
endmodule

module d;
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
