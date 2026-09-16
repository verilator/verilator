// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); $stop; end while(0);

// Fork branch that waits forever at wait(0).
`define FORK_BRANCH_WAIT_FOREVER do begin; ++hanged_branches; wait(0); $fatal(2, "should not get here"); end while(0);
// Fork branch that finishes without waiting.
`define FORK_BRANCH_FINISH do begin; ++finished_branches; end while(0);
// verilog_format: on

module t;
  int hanged_branches = 0;
  int finished_branches = 0;
  int resumed_joins = 0;

  initial begin : join_any2
    fork
      #10 `FORK_BRANCH_WAIT_FOREVER;
      #10 `FORK_BRANCH_WAIT_FOREVER;
      `FORK_BRANCH_FINISH;
    join_any
    resumed_joins++;
  end

  initial begin : join_any3
    fork
      `FORK_BRANCH_WAIT_FOREVER;
      `FORK_BRANCH_WAIT_FOREVER;
      #10 `FORK_BRANCH_FINISH;
    join_any
    resumed_joins++;
  end

  initial begin : join_none1
    fork
      `FORK_BRANCH_WAIT_FOREVER
      `FORK_BRANCH_WAIT_FOREVER
    join_none
    resumed_joins++;
  end

  initial begin
    #15;
    `checkd(hanged_branches, 6);
    `checkd(finished_branches, 2);
    `checkd(resumed_joins, 3);
    $info("*-* All Finished *-*");
    $finish;
  end
endmodule
