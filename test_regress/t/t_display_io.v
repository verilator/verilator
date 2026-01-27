// DESCRIPTION: Verilator: $display() test for %l
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2021 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   o,
   // Inputs
   i
   );

   input logic [95:0] i;
   output logic [95:0] o;

   string         a_s;

   initial begin
      o = ~i;
      $sformat(a_s, "%h", i);
      $display(a_s);
      $sformat(a_s, "%h", o);
      $display(a_s);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
