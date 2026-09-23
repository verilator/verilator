// DESCRIPTION: Verilator: Cycle delays of synchronous drives count the target clocking block
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// No default clocking is needed for a cycle delay in a drive
module sub (
    input bit clk,
    output bit [1:0] q
);
  clocking cb @(posedge clk);
    output q;
  endclocking
  initial begin
    @(cb);
    cb.q <= ##1 2;
  end
endmodule

module t;
  bit clk;
  bit slow_clk;
  bit [1:0] v;
  bit [1:0] q;
  string v_log;
  string q_log;

  always #5 clk = ~clk;
  always #20 slow_clk = ~slow_clk;

  default clocking slow @(posedge slow_clk);
  endclocking

  clocking fast @(posedge clk);
    output v;
  endclocking

  sub sub (
      .clk,
      .q
  );

  always @(v) if ($time != 0) v_log = {v_log, $sformatf("%0d@%0d ", v, $time)};
  always @(q) if ($time != 0) q_log = {q_log, $sformatf("%0d@%0d ", q, $time)};

  initial begin
    @(fast);
    // Counts cycles of 'fast', not of the default clocking (IEEE 1800-2023 14.16)
    fast.v <= ##2 1;
    #50;
    `checks(v_log, "1@25 ")
    `checks(q_log, "2@15 ")
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
