// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// Checks that randomize() with a non-trivial scalar constraint (exactly N
// set bits, a non-contiguous solution set scattered across the domain)
// reaches nearly all of the solution space, not just a lucky subset of it. Each
// sample is also printed so the driver can check the distribution's
// uniformity (Jensen-Shannon divergence) from the samples, not just coverage.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=[%0d:%0d]\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

module t;
  class C;
    rand bit [7:0] x;
    constraint c { $countones(x) == 4; }
  endclass

  localparam int NUM_SOLUTIONS = 70;  // C(8,4)
  localparam int NUM_ITERS = 25 * NUM_SOLUTIONS;

  localparam int MIN_COVERAGE_PCT = 90;
  localparam int MAX_COVERAGE_PCT = 100;
  localparam int MIN_DISTINCT = (NUM_SOLUTIONS * MIN_COVERAGE_PCT) / 100;
  localparam int MAX_DISTINCT = (NUM_SOLUTIONS * MAX_COVERAGE_PCT) / 100;

  initial begin
    automatic C c = new;
    automatic bit seen[256];
    automatic int distinct = 0;
    automatic int ok;
    for (int i = 0; i < NUM_ITERS; ++i) begin
      ok = c.randomize();
      `checkd(ok, 1);
      `checkd($countones(c.x), 4);
      if (!seen[c.x]) begin
        seen[c.x] = 1'b1;
        distinct++;
      end
      $display("%0d", c.x);
    end
    `check_range(distinct, MIN_DISTINCT, MAX_DISTINCT);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
