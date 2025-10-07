// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

int x = 0;

task task_fork();
  begin : blk
    fork : fork_blk
      begin
        x = 1;
        disable blk;
        x = 2;
      end
    join_none
  end
endtask

module t;
  initial begin
    task_fork();
    if (x != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
