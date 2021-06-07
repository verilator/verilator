// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   r
   );
   input real r;

   initial begin
      $display("%g", $cos($cos($cos($cos($cos($cos($cos($cos(r + 0.1)))))))));
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
