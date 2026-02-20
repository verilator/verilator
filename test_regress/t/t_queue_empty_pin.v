// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t;
   task tsk(int q[] = {});
      if (q.size != 0) $stop;
   endtask

   initial begin
      tsk();

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
