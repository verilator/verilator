// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0)
// verilog_format: on

task disable_fork_blk;
  disable t.init.fork_blk;
endtask

task automatic disable_join_none;
  disable t.join_case.f2;
endtask

module t;

  initial begin : init
    int x;
    fork : fork_blk
      begin
        x = 1;
        disable_fork_blk();
        #1;
        x = 2;
      end
      begin
        #1;
        x = 3;
      end
    join
    `checkd(x, 1);
  end

  initial begin : join_case
    int jx;
    int jy;
    fork : f2
      begin
        #1;
        jx = 1;
      end
      begin
        #10;
        jy = 1;
      end
    join_none
    #2;
    disable_join_none();
    #12;
    `checkd(jx, 1);
    `checkd(jy, 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
