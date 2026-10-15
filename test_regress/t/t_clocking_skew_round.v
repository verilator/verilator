// DESCRIPTION: Verilator: Clocking output skews rounded to simulation time precision
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface scaled_if (
    input bit clk
);
  timeunit 10ns; timeprecision 1ns;

  bit zero_skew;
  bit half_skew;
  bit nonzero_skew;
  clocking cb @(posedge clk);
    output #0.04 zero_skew;
    output #0.05 half_skew;
    output #0.1 nonzero_skew;
  endclocking
endinterface

module t;
  timeunit 1ns; timeprecision 1ns;

  bit clk;
  bit expected;
  bit zero_skew;
  bit below_half;
  bit half_skew;
  bit above_half;
  scaled_if scaled (.clk);

  always #5 clk = ~clk;

  clocking cb @(posedge clk);
    output #0.1 zero_skew;
    output #0.49 below_half;
    output #0.5 half_skew;
    output #0.51 above_half;
  endclocking

  always @(posedge clk) begin
    expected = ~expected;
    cb.zero_skew <= expected;
    cb.below_half <= expected;
    cb.half_skew <= expected;
    cb.above_half <= expected;
    scaled.cb.zero_skew <= expected;
    scaled.cb.half_skew <= expected;
    scaled.cb.nonzero_skew <= expected;
    // Effective-zero skews must be visible before Postponed observers run.
    $strobe("%0t: %0d %0d %0d %0d %0d %0d %0d", $time, zero_skew, below_half, half_skew,
            above_half, scaled.zero_skew, scaled.half_skew, scaled.nonzero_skew);
  end

  always @(negedge clk) begin
    `checkd(zero_skew, expected)
    `checkd(below_half, expected)
    `checkd(half_skew, expected)
    `checkd(above_half, expected)
    `checkd(scaled.zero_skew, expected)
    `checkd(scaled.half_skew, expected)
    `checkd(scaled.nonzero_skew, expected)
  end

  initial begin
    #31;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
