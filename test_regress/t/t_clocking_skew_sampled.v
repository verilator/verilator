// DESCRIPTION: Verilator: Skewed clocking drives evaluate their time step once
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit clk;
  bit q;

  always #5 clk = ~clk;

  clocking cb @(posedge clk);
    output #1 q;
  endclocking

  always @(cb) cb.q <= ~q;

  // clk rises at 5, 15, ..., so it is sampled low throughout these time steps (IEEE 1800-2023
  // 16.5.1). The skewed drive must not evaluate a time step again, sampling clk high.
  always_comb if ($time % 10 == 5) `checkd($sampled(clk), 1'b0)

  initial begin
    #50;
    `checkd(q, 1'b1)
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
