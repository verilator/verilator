// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Based on ivtest's pr540.v by Steve Williams.
module t;
   bit fail = 0;
   bit abort = 0;

   initial begin
      abort = 1; // Set here so it's non-constant, otherwise ifs gets folded
      begin: block
         if (abort) disable block;
         fail = 1; // Don't try to move this in order to merge the 2 ifs
         if (abort) $display("unreachable");
      end
      if (fail) $error("block disable FAILED");
      $write("*-* All Finished *-*\n");
      $finish(0);
   end
endmodule
