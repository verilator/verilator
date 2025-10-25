// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%t %%Error: %s:%0d:  got=%0d exp=%0d\n", $time, `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  bit clk = 0;
  always #10 clk = ~clk;

  // Case A
  bit [3:0] cnt_A = 0;
  task task_A();
    $display("%t %m enter", $time);
    cnt_A = 0;
    repeat (2) @(posedge clk);
    for (int i = 0; i < 8; i++) begin : loop
      $display("%t %m inc %d", $time, i);
      ++cnt_A;
      repeat (2) @(posedge clk);
    end
    $display("%t %m inc final", $time);
    ++cnt_A;
    repeat (2) @(posedge clk);
    $display("%t %m exit", $time);
  endtask

  // Case B - Same, with 'repeat' unrolled
  bit [3:0] cnt_B = 0;
  task task_B();
    $display("%t %m enter", $time);
    cnt_B = 0;
    @(posedge clk);
    @(posedge clk);
    for (int i = 0; i < 8; i++) begin : loop
      ++cnt_B;
      @(posedge clk);
      @(posedge clk);
    end
    $display("%t %m inc final", $time);
    ++cnt_B;
    @(posedge clk);
    @(posedge clk);
    $display("%t %m exit", $time);
  endtask

  initial begin
    task_A();
    $display("%t taks_A return 1", $time);
    task_A();
    $display("%t taks_A return 2", $time);
  end

  initial begin
    task_B();
    $display("%t taks_B return 1", $time);
    task_B();
    $display("%t taks_B return 2", $time);

    #100;
    $write("*-* All Finished *-*\n");
    $finish;
  end

  always_ff @(posedge clk) begin
    #1 `checkd(cnt_A, cnt_B);
  end

endmodule
