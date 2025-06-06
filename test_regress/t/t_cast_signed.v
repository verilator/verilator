// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   logic [7:0] smaller;
   logic [15:0] bigger;
   typedef logic [15:0] bigger_t;

   initial begin
      smaller = 8'hfa;
      bigger = bigger_t'(signed'(smaller));
      $display("%x", bigger); // NOCOMMIT
      if (bigger != 16'hfffa) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
