// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   initial begin
      for (int i = 0; i < 3; i++) begin
         begin : blk
            int x = 0;
            fork : fork_blk
               begin
                  x = 1;
                  #2;
                  x = 2;
               end
            join_none
            #1;
            if (i < 2) disable fork_blk;
            #2;
            if (i < 2 && x != 1) $stop;
            if (i == 2 && x != 2) $stop;
         end
      end
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
