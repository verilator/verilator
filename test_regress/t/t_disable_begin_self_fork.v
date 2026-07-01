// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A named begin block that contains a fork still has to behave like a normal
// named block when it disables itself: execution resumes after the block, so
// statements after the disable inside the block must not run. All activity
// enabled within the block, including forked child processes, must terminate.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  bit after_disable = 1'b0;
  bit fork_survived = 1'b0;

  initial begin : blk
    fork
      begin
        #5;
        fork_survived = 1'b1;
      end
    join_none
    #1;
    disable blk;
    after_disable = 1'b1;
  end

  initial begin
    #10;
    `checkd(after_disable, 1'b0);
    `checkd(fork_survived, 1'b0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
