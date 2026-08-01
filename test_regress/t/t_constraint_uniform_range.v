// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 18.5.9 requires every legal value combination to be equally
// probable.  For a single variable constrained to a range that means every
// value in the range comes up equally often.
//
// A range that is a power-of-2 bit-aligned block does come out uniform.  Any
// other range does not: the runtime pins each free bit to a random target, so
// bit k is set half the time whatever fraction of the legal values actually
// have it set.  Over [0:16] only one of the seventeen legal values has bit 4
// set, so that one value takes about half of all draws.
//
// The $urandom_range case is a control that involves no solver, and the
// [0:15] and [0:31] cases are controls that the current mechanism handles
// correctly.  All three pass; they are here so that a failure elsewhere is
// clearly not the harness.  See issue #8024.

// verilog_format: off
`define stop $stop
`define check_range(nam,gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d: %s: got=%0d exp=%0d..%0d\n", `__FILE__,`__LINE__, nam, (gotv), (minv), (maxv)); fails++; end while(0);
// verilog_format: on

`define N 2000

// Every legal value must be drawn between a third and twice the uniform
// share.  The tightest range here has 16 legal values, where Binomial(`N,
// 1/16) has mean 125 and standard deviation 10.8, so the band is over 7 sigma
// either way and a uniform solver passes on any seed.
//
// The low bound is a third rather than a half because the two are not
// independent: if one value takes half of all draws, the rest necessarily
// average half the uniform share, which would make the low bound fire
// marginally on every one of them.  A third keeps the reported failure on the
// value that is actually over-represented.
`define LO_NUM 1
`define LO_DEN 3
`define HI_NUM 2
`define HI_DEN 1

class InsideAligned16;
  rand int value;
  constraint c {value inside {[0 : 15]};}
endclass

class InsideAligned32;
  rand int value;
  constraint c {value inside {[0 : 31]};}
endclass

// Seventeen legal values.  Only value 16 has bit 4 set.
class InsideOffByOne;
  rand int value;
  constraint c {value inside {[0 : 16]};}
endclass

class InsideRange;
  rand int value;
  constraint c {value inside {[1 : 20]};}
endclass

// The same legal set written without 'inside'.
class CompareRange;
  rand int value;
  constraint c {
    value >= 1;
    value <= 20;
  }
endclass

// The same legal set asked for as a soft constraint inside a wider hard one.
class SoftRange;
  rand int value;
  constraint c {value inside {[0 : 100]};}
endclass

module t;
  int fails;
  int hist  [0:127];

  function automatic void reset_hist();
    foreach (hist[i]) hist[i] = 0;
  endfunction

  function automatic void tally(input int value, input int lo, input int hi);
    if (value < lo || value > hi) begin
      $write("%%Error: value %0d outside [%0d:%0d]\n", value, lo, hi);
      fails++;
      return;
    end
    hist[value]++;
  endfunction

  // Report every legal value, then flag the ones outside the band.
  function automatic void check_uniform(input string name, input int lo, input int hi);
    automatic int nvals = hi - lo + 1;
    automatic int expect_each = `N / nvals;
    automatic int minv = hist[lo];
    automatic int maxv = hist[lo];
    for (int v = lo; v <= hi; v++) begin
      if (hist[v] < minv) minv = hist[v];
      if (hist[v] > maxv) maxv = hist[v];
    end
    $display("%-28s [%0d:%0d] %0d values, expected %0d each, got min=%0d max=%0d", name, lo, hi,
             nvals, expect_each, minv, maxv);
    for (int v = lo; v <= hi; v++)
      `check_range(name, hist[v], expect_each * `LO_NUM / `LO_DEN, expect_each * `HI_NUM / `HI_DEN)
  endfunction

  initial begin
    automatic InsideAligned16 a16 = new;
    automatic InsideAligned32 a32 = new;
    automatic InsideOffByOne o17 = new;
    automatic InsideRange ir = new;
    automatic CompareRange cr = new;
    automatic SoftRange sr = new;
    int i;
    int r;

    // Control: no solver involved.
    reset_hist();
    for (i = 0; i < `N; i++) tally($urandom_range(16, 0), 0, 16);
    check_uniform("$urandom_range 0..16", 0, 16);

    // Control: power-of-2 bit-aligned blocks are handled correctly.
    reset_hist();
    for (i = 0; i < `N; i++) begin
      r = a16.randomize();
      `check_range("randomize [0:15]", r, 1, 1)
      tally(a16.value, 0, 15);
    end
    check_uniform("inside [0:15]", 0, 15);

    reset_hist();
    for (i = 0; i < `N; i++) begin
      r = a32.randomize();
      `check_range("randomize [0:31]", r, 1, 1)
      tally(a32.value, 0, 31);
    end
    check_uniform("inside [0:31]", 0, 31);

    // One value wider than a power-of-2 block, which is the worst case.
    reset_hist();
    for (i = 0; i < `N; i++) begin
      r = o17.randomize();
      `check_range("randomize [0:16]", r, 1, 1)
      tally(o17.value, 0, 16);
    end
    check_uniform("inside [0:16]", 0, 16);

    reset_hist();
    for (i = 0; i < `N; i++) begin
      r = ir.randomize();
      `check_range("randomize [1:20]", r, 1, 1)
      tally(ir.value, 1, 20);
    end
    check_uniform("inside [1:20]", 1, 20);

    // Not specific to 'inside'; both lower to the same comparisons.
    reset_hist();
    for (i = 0; i < `N; i++) begin
      r = cr.randomize();
      `check_range("randomize >=1 <=20", r, 1, 1)
      tally(cr.value, 1, 20);
    end
    check_uniform("value >= 1; value <= 20", 1, 20);

    // Soft constraints take the same path.
    reset_hist();
    for (i = 0; i < `N; i++) begin
      r = sr.randomize() with {soft value inside {[1 : 20]};};
      `check_range("randomize soft [1:20]", r, 1, 1)
      tally(sr.value, 1, 20);
    end
    check_uniform("soft inside [1:20]", 1, 20);

    if (fails != 0) begin
      $write("%%Error: %0d check(s) outside tolerance\n", fails);
      `stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
