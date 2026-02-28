// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
   initial begin
      begin : blk
         int x;
         fork
            begin
               #1;
               disable begin_blk;
            end
            begin : begin_blk
               x = 1;
               #2;
               x = 2;
            end
         join_none
         #3;
         if (x != 1) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
