// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class RecFork;
   int cnt = 0;
   task run(int n);
      if (n > 0) begin
         cnt++;
         fork
            run(n - 1);
         join
      end
   endtask
endclass

module t;
   initial begin
      automatic RecFork rec = new;
      rec.run(7);
      if (rec.cnt != 7) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
  end
endmodule
