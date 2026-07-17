// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// $past staging in assertion actions and non-final function/task callers.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0h exp=%0h\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  bit clk = 0;
  int cyc = 0;

  always #1 clk = ~clk;

  default clocking cb @(posedge clk);
  endclocking

  // $past in an assertion action returns the previous sampled value
  bit act_data = 0;
  bit history[0:4] = '{default: 0};
  int history_count = 0;

  always @(posedge clk) act_data <= ~act_data;

  assert property (@(posedge clk) 1'b1 ##1 1'b1) begin
    if (history_count < 5) history[history_count] = $past(act_data);
    history_count++;
  end

  // Non-final function/task callers retain the normal $past lowering
  bit data = 0;

  function automatic bit fpast();
    return $past(data);
  endfunction

  task automatic tpast(output bit result);
    result = $past(data);
  endtask

  always @(posedge clk) begin
    cyc <= cyc + 1;
    data <= ~data;
  end

  always @(negedge clk) begin
    bit direct;
    bit via_task;
    direct = $past(data);
    tpast(via_task);
    if (fpast() !== direct || via_task !== direct) begin
      $display("%%Error: direct=%0b function=%0b task=%0b", direct, fpast(), via_task);
      $fatal;
    end
  end

  initial begin
    repeat (6) @(negedge clk);
    `checkd(history_count, 5);
    `checkd(history[0], 0);
    `checkd(history[1], 1);
    `checkd(history[2], 0);
    `checkd(history[3], 1);
    `checkd(history[4], 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
