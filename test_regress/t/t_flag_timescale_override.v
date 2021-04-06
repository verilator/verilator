// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`timescale 1s/1s

module t;
   sub sub ();
   initial begin
      $printtimescale;
      sub.pts();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module sub;
   task pts;
      $printtimescale;
   endtask
endmodule
