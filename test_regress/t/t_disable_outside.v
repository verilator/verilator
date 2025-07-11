// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   initial begin
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
         disable fork_blk;
         #2;
         if (x != 1) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
