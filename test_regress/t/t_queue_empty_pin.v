// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   task tsk(int q[] = {});
      if (q.size != 0) $stop;
   endtask

   initial begin
      tsk();

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
