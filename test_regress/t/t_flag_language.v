// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   // See also t_preproc_kwd.v

   integer bit; initial bit = 1;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
