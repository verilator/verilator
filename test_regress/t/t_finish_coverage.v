// DESCRIPTION: Verilator: Basic-block coverage across $finish propagation
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define STRINGIFY(x) `"x`"
// verilog_format: on

module t;
  int branch_after;
  int initial_after;
  int leaf_after;
  int loop_after;
  int wrapper_after;

  class base_runner;
    virtual task run();
    endtask
  endclass

  class finish_runner extends base_runner;
    task run();
      $root.t.leaf();
    endtask
  endclass

  base_runner runner;
  finish_runner derived_runner;

  task automatic leaf();  // COVER_TARGET:block COVER_LINE_HIT
    int index = 0;
    repeat (1) begin  // COVER_TARGET:block
      if ((index == 0) && (loop_after == 0)) begin  // COVER_TARGET:if COVER_EXPR_TARGET COVER_LINE_HIT
        case (index)
          0: begin  // COVER_TARGET:case COVER_LINE_HIT
            $finish;  // COVER_LINE_HIT
            leaf_after++;  // COVER_LINE_MISS
          end
          default: ;
        endcase
        branch_after++;  // COVER_LINE_MISS
      end
      loop_after++;  // COVER_LINE_MISS
    end
  endtask

  task automatic wrapper();  // COVER_TARGET:block
    runner.run();  // COVER_LINE_HIT
    wrapper_after++;  // COVER_LINE_MISS
  endtask

  initial begin  // COVER_TARGET:block
    derived_runner = new;
    runner = derived_runner;
`ifdef TRACE_COVERAGE_TEST
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars(0, t);
`endif
    wrapper();  // COVER_LINE_HIT
    initial_after++;  // COVER_LINE_MISS
  end

  final begin
    `checkd(branch_after, 0);
    `checkd(initial_after, 0);
    `checkd(leaf_after, 0);
    `checkd(loop_after, 0);
    `checkd(wrapper_after, 0);
    $write("*-* All Finished *-*\n");
  end
endmodule
