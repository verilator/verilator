// DESCRIPTION: Verilator: Signal driven by two clocking blocks
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit clk;
  bit [1:0] j;
  string j_log;

  always #5 clk = ~clk;

  // A DDR device model, the variable takes the value most recently driven by either clocking
  // block (IEEE 1800-2023 14.16.2)
  clocking pe @(posedge clk);
    output j;
  endclocking
  clocking ne @(negedge clk);
    output j;
  endclocking

  // Ignore the evaluation at initialization
  always @(j) if ($time != 0) j_log = {j_log, $sformatf("%0d@%0d ", j, $time)};

  initial begin
    @(pe);
    pe.j <= 1;
    @(ne);
    ne.j <= 2;
    @(pe);
    pe.j <= 3;
    @(ne);
    ne.j <= 1;
    #5;
    `checks(j_log, "1@5 2@10 3@15 1@20 ")
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
