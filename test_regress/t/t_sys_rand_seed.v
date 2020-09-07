// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   int valuea;
   int valueb;

   initial begin
      valuea = $random(10);
      valueb = $random(10);
      if (valuea !== valueb) $stop;
      valuea = $urandom(10);
      valueb = $urandom(10);
      if (valuea !== valueb) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
