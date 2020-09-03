// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (
   );

   // Overrides standard class
   class process;
   endclass
   class mailbox;
   endclass
   class semaphore;
   endclass

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
