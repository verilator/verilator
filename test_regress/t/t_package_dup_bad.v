// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package pkg;
   localparam PARAM = 10;
endpackage

package pkg;
   localparam PARAM = 10;
endpackage

module sub import pkg::*;
   #( ) ();
endmodule

package pkg;
endpackage

package pkg;
endpackage

module t (/*AUTOARG*/);
   sub sub ();
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
