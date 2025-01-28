// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   int x = 1;
endclass

task init_set_2 (output Cls c);
   c = new;
   c.x = 2;
endtask

module t (/*AUTOARG*/);

   initial begin
      Cls cls_q[$];
      init_set_2(cls_q[0]);
      if (cls_q[0].x != 2) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
