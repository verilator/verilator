// DESCRIPTION: Verilator: Verilog Test module
//
// Use this file as a template for submitting bugs, etc.
// This module takes a single clock input, and should either
//      $write("*-* All Finished *-*\n");
//      $finish;
// on success, or $stop.
//
// The code as shown applies a random vector to the Test
// module, then calculates a CRC on the Test module's outputs.
//
// **If you do not wish for your code to be released to the public
// please note it here, otherwise:**
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 ____YOUR_NAME_HERE____.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   int x;
   int y;

   function void f;
      x = x + 1;
      if (x == 10) return;
      y = y + 1;
   endfunction

   initial begin
      while (1) begin : whilea
         x = x + 1;
         if (x == 10) break;
         y = y + 1;
      end
      while (1) begin : whileb
         x = x + 1;
         if (x == 10) continue;
         y = y + 1;
      end
   end
endmodule
