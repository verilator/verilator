// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define N 3

class Cls;
   task runforks(integer n);
      for (integer i = 0; i < n; i++) fork
         #1 $stop;
      join_none
   endtask
endclass

module t;
   Cls cls = new;

   initial begin
      // run forks
      for (integer i = 0; i < `N; i++) fork
         #1 $stop;
      join_none

      // run forks inside a method
      cls.runforks(`N);

      // run forks in forks
      for (integer i = 0; i < `N; i++) fork
         for (integer j = 0; j < `N; j++) fork
            #1 $stop;
         join_none
      join_none

      for (integer i = 0; i < `N; i++) fork
         cls.runforks(`N);
      join_none

      // kill them all
      disable fork;

      // check if we can still fork
      fork
         #2 $write("*-* All Finished *-*\n");
         #3 $finish;
      join_none
   end
endmodule
