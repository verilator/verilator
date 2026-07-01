// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A disable of a named fork inside one dynamic task invocation must kill
// branches of the same syntactic fork in every concurrent invocation of that
// task. IEEE 1800-2023 9.6.2 says disabling an automatic task or a block inside
// an automatic task proceeds as for regular tasks for all concurrent executions
// of the task.
//
// The cross-module case checks the complementary instance scoping rule: the same
// task declaration can be instantiated under different module instances in
// different wrapper modules, and disabling the named fork in one instance must
// not terminate the other instance's fork.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module child_task_mod (
    input bit do_disable,
    output bit survived,
    output bit task_done
);

  task automatic run();
    fork : fork_blk
      begin
        if (do_disable) begin
          #1;
          disable fork_blk;
          $stop;
        end
        else begin
          #6;
        end
      end
      begin
        #5;
        survived = 1'b1;
      end
    join
    task_done = 1'b1;
  endtask

  initial run();
endmodule

module disable_wrapper (
    output bit survived,
    output bit task_done
);
  child_task_mod child (
      .do_disable(1'b1),
      .survived(survived),
      .task_done(task_done)
  );
endmodule

module keep_wrapper (
    output bit survived,
    output bit task_done
);
  child_task_mod child (
      .do_disable(1'b0),
      .survived(survived),
      .task_done(task_done)
  );
endmodule

module t;

  bit [1:0] survived_a = 2'b00;
  bit [1:0] survived_b = 2'b00;
  bit [1:0] task_done = 2'b00;
  bit wrapper_disable_survived;
  bit wrapper_disable_done;
  bit wrapper_keep_survived;
  bit wrapper_keep_done;

  disable_wrapper wrapper0 (
      .survived(wrapper_disable_survived),
      .task_done(wrapper_disable_done)
  );

  keep_wrapper wrapper1 (
      .survived(wrapper_keep_survived),
      .task_done(wrapper_keep_done)
  );

  task automatic run(input int id, input bit do_disable);
    fork : fork_blk
      begin
        if (do_disable) begin
          #1;
          disable fork_blk;
          $stop;
        end
        else begin
          #6;
          survived_a[id] = 1'b1;
        end
      end
      begin
        if (do_disable) begin
          #5 $stop;
        end
        else begin
          #6;
          survived_b[id] = 1'b1;
        end
      end
    join
    task_done[id] = 1'b1;
  endtask

  initial begin
    fork
      run(0, 1'b1);
      run(1, 1'b0);
    join
    #1;
    `checkd(task_done, 2'b11);
    `checkd(survived_a, 2'b00);
    `checkd(survived_b, 2'b00);
    #6;
    `checkd(wrapper_disable_done, 1'b1);
    `checkd(wrapper_keep_done, 1'b1);
    `checkd(wrapper_disable_survived, 1'b0);
    `checkd(wrapper_keep_survived, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
