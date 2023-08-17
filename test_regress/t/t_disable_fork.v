// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define N 5

module t;
   integer n = 0;

   initial begin
      for (integer i = 0; i < `N; i++) fork
            #1 n = n + 1;
      join_none
      disable fork;
      #2;
      if (n > 0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
