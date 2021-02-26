// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by engr248.
// SPDX-License-Identifier: CC0-1.0

module \foo$bar (/*AUTOARG*/);
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
