// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

task disable_fork_blk;
   disable t.init.fork_blk;
endtask

module t(/*AUTOARG*/);

   initial begin : init
      int x = 0;
      fork : fork_blk
         begin
            x = 1;
            disable_fork_blk();
            x = 2;
         end
         begin
            #1;
            x = 3;
         end
      join
      if (x != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
