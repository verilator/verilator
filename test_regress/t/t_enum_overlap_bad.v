// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   enum { e0,
          e1,
          e2,
          e1b=1
          } BAD1;

   initial begin
      $stop;
   end

endmodule
