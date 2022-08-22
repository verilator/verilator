// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
   int counter = 0;

   // As Verilator doesn't support recursive calls, let's use macros to generate tasks
   `define FORK2_END(i) \
   task fork2_``i; \
      #1 counter++; \
   endtask

   `define FORK2(i, j) \
   task fork2_``i; \
      fork \
          #1 fork2_``j; \
          #1 fork2_``j; \
      join \
   endtask

   `FORK2_END(0);
   `FORK2(1, 0);
   `FORK2(2, 1);
   `FORK2(3, 2);
   `FORK2(4, 3);
   `FORK2(5, 4);
   `FORK2(6, 5);
   `FORK2(7, 6);
   `FORK2(8, 7);

   initial begin
      fork2_8;
`ifdef TEST_VERBOSE
      $write("[%0t] process counter == %0d\n", $time, counter);
`endif
      if (counter != 1 << 8) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
endmodule
