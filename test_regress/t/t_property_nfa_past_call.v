// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Non-final function/task callers retain the normal $past lowering.

module t;

  bit clk = 0;
  bit data = 0;
  int cyc = 0;

  always #1 clk = ~clk;

  default clocking cb @(posedge clk);
  endclocking

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
    if (cyc == 4) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
