// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
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
