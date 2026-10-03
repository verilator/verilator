// DESCRIPTION: Verilator: Pending intra-assignment NBAs keep their own values
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
  int x;
  bit [1:0] q;
  string x_log;
  string q_log;

  always #5 clk = ~clk;

  default clocking cb @(posedge clk);
    output q;
  endclocking

  task automatic pulse(bit [1:0] v);
    cb.q <= ##2 v;
  endtask

  always @(x) if ($time != 0) x_log = {x_log, $sformatf("%0d@%0d ", x, $time)};
  always @(q) if ($time != 0) q_log = {q_log, $sformatf("%0d@%0d ", q, $time)};

  // Each pending update keeps the value it was scheduled with
  initial begin
    for (int i = 1; i <= 3; ++i) begin
      x <= #5 i;
      #1;
    end
  end

  // Each pending drive from the same inlined call counts its own cycles
  initial begin
    for (int i = 1; i <= 2; ++i) begin
      @(cb);
      pulse(2'(i));
    end
  end

  initial begin
    #50;
    `checks(x_log, "1@5 2@6 3@7 ")
    `checks(q_log, "1@25 2@35 ")
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
