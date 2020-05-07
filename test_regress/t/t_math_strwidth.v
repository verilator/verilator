// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008-2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   reg [4*8:1] strg;

   initial begin
      strg = "CHK";
      if (strg != "CHK") $stop;
      if (strg == "JOE") $stop;
      $write("String = %s = %x\n", strg, strg);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
