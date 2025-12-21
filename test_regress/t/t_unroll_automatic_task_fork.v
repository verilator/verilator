// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Targets issue 6194

module t;

  logic clk;

  initial begin
    clk = 0;
    forever #(1) clk = ~clk;
  end

  task automatic task_example(int module_id, int channel);
    $display("task_example start:  module %0d, channel %0d", module_id, channel);
    @(posedge clk);
    $display("task_example end:  module %0d, channel %0d", module_id, channel);
  endtask

  initial begin : initial_block
    for (int m = 0; m < 2; m++) begin
      for (int i = 0; i < 2; i++) begin : forked_loop
        automatic int mod = m;
        automatic int ch = i;
        fork : forked_block
          task_example(mod, ch);
        join
      end
    end

    #10 $write("*-* Test 1 Finished *-*\n");

    for (int m = 0; m < 2; m++) begin
      for (int i = 0; i < 2; i++) begin : forked_loop
        automatic int mod = m;
        automatic int ch = i;
        fork : forked_block
          task_example(mod, ch);
        join_any
      end
    end

    #10 $write("*-* Test 2 Finished *-*\n");

    for (int m = 0; m < 2; m++) begin
      for (int i = 0; i < 2; i++) begin : forked_loop
        automatic int mod = m;
        automatic int ch = i;
        fork : forked_block
          task_example(mod, ch);
          $display("extra statement");
        join_any
      end
    end

    #10 $write("*-* Test 3 Finished *-*\n");

    for (int m = 0; m < 2; m++) begin
      for (int i = 0; i < 2; i++) begin : forked_loop
        automatic int mod = m;
        automatic int ch = i;
        fork : forked_block
          task_example(mod, ch);
        join_none
      end
    end

    #10 $write("*-* Test 4 Finished *-*\n");

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
