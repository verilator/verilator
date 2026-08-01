// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 18.5.9 requires uniformity over legal value *combinations*,
// not just over the values of one variable.  Here x + y == 10 with two 4-bit
// variables has exactly 11 solutions, x = 0..10 with y = 10 - x, so each
// value of x should come up about as often as any other.
//
// Unlike the single-variable ranges in t_constraint_uniform_range, the skew
// here is spread across the bins rather than concentrated in one value, so a
// per-value band wide enough not to be flaky does not catch it.  This test
// uses a chi-square goodness-of-fit statistic instead.  With 11 bins there
// are 10 degrees of freedom, where a uniform solver averages about 10 and
// exceeds 60 with probability about 4e-9.  Verilator scores in the low
// hundreds.  See issue #8024.

// verilog_format: off
`define stop $stop
`define check_range(nam,gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d: %s: got=%0d exp=%0d..%0d\n", `__FILE__,`__LINE__, nam, (gotv), (minv), (maxv)); fails++; end while(0);
// verilog_format: on

`define N 2000
`define SOLUTIONS 11
`define CHI2_MAX 60

class Pair;
  rand bit [3:0] x, y;
  constraint c {x + y == 10;}
endclass

module t;
  int fails;
  int hist  [0:15];

  initial begin
    automatic Pair p = new;
    real expect_each;
    real chi2;
    real diff;
    int i;
    int r;

    foreach (hist[i]) hist[i] = 0;

    for (i = 0; i < `N; i++) begin
      r = p.randomize();
      `check_range("randomize", r, 1, 1)
      // Every solution must satisfy the constraint and lie in x = 0..10.
      `check_range("x + y", int'(p.x) + int'(p.y), 10, 10)
      `check_range("x", int'(p.x), 0, 10)
      hist[p.x]++;
    end

    expect_each = real'(`N) / real'(`SOLUTIONS);
    chi2 = 0.0;
    $write("x counts (expected %0.1f each):", expect_each);
    for (i = 0; i < `SOLUTIONS; i++) begin
      $write(" %0d", hist[i]);
      diff = real'(hist[i]) - expect_each;
      chi2 += (diff * diff) / expect_each;
    end
    $write("\n");
    $display("chi-square %0.1f over %0d bins, tolerated up to %0d", chi2, `SOLUTIONS, `CHI2_MAX);

    if (chi2 > real'(`CHI2_MAX)) begin
      $write("%%Error: %s:%0d: x distribution is not uniform over the 11 solutions\n", `__FILE__,
             `__LINE__);
      fails++;
    end

    if (fails != 0) begin
      $write("%%Error: %0d check(s) outside tolerance\n", fails);
      `stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
