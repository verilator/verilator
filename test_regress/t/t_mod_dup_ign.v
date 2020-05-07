// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   sub sub ();
endmodule

module sub;
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

// verilator lint_off MODDUP
module sub;
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
