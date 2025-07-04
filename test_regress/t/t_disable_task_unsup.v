// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

int x = 0;

task increment_x;
   x++;
   #2;
   x++;
endtask

module t(/*AUTOARG*/);

   initial begin
      fork
         increment_x();
         #1 disable increment_x;
      join
      if (x != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
