// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module liblib_a;
   liblib_b b ();
endmodule

module liblib_b;
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module liblib_c;
   // Unused
   initial $stop;
   liblib_d d ();
endmodule

module liblib_d;
   // Unused
   initial $stop;
endmodule
