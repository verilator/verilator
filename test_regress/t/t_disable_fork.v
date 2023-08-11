// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define N 5

module t;
   process p = process::self();
   integer n = 0;
   bit b = 0;

   initial begin
      for (integer i = 0; i < `N; i++) fork
         begin
            wait (b);
            n++;
         end
      join_none
      p.disable_fork();
      b = 1;
      #1;
      if (n > 0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
