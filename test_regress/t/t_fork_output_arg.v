// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int x = 100;
   task get_x(output int arg);
      arg = x;
   endtask
endclass

task automatic test;
   int o;
   Cls c = new;
   fork
      c.get_x(o);
   join_any
   if (o != 100) $stop;
endtask

module t();
   initial begin
      test();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
