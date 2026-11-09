// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Disable by name of a task or a named block is implemented with a detached
// process, so it requires --timing

module t;
  task automatic tsk;
    disable tsk;
  endtask

  initial begin
    tsk();
    fork
      begin : blk
        #1;
      end
    join_none
    disable blk;
    $finish;
  end
endmodule
