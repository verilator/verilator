// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   typedef struct packed { bit m; } struct_t;
   struct_t s;

   initial begin
      s.nfmember = 0; // Member not found
      $finish;
   end
endmodule
