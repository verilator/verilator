// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A 'dist' whose value items are non-constant expressions must still honor its
// weights (IEEE 1800-2023 18.5.4).  Non-'rand' class members are state
// variables for the call and hold a fixed value while it runs, so
// 'x dist {lo :/ 10, ...}' is as well defined as 'x dist {3 :/ 10, ...}'.
//
// Before the accompanying fix the weights were dropped for such a 'dist' and
// the draw came out uniform over the set.
//
// Only the single-value items are affected.  The controls below are the same
// 'dist' written with literal items, and a 'dist' whose only non-constant
// parts are range bounds; both were already weighted correctly.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
`define check_tol(gotv,expv) `check_range((gotv), (expv)*(100-`TOL_PCT)/100, (expv)*(100+`TOL_PCT)/100)
`define check_hist `check_tol(nlo, `N * `W_LO / `W_TOT) `check_tol(nmid, `N * `W_MID / `W_TOT) `check_tol(nhi, `N * `W_HI / `W_TOT)
// verilog_format: on

// The bands only have to separate the weighted draw from the uniform one the
// bug produces, so they are deliberately loose: every check below sits at four
// sigma or more, while the buggy value is far outside.  A tighter band would
// turn any future change to solver call order into a spurious failure.
`define N 1000
`define TOL_PCT 40
`define W_LO 10
`define W_MID 3
`define W_HI 2
`define W_TOT (`W_LO + `W_MID + `W_HI)

// Everything literal.  Control.
class LiteralItems;
  rand bit [3:0] x;
  constraint c {
    x dist {
      3 :/ `W_LO,
      [4 : 9] :/ `W_MID,
      10 :/ `W_HI
    };
  }
endclass

// Only the range bounds are non-constant.  Control: these stay weighted.
class VarBounds;
  rand bit [3:0] x;
  bit [3:0] lo = 3;
  bit [3:0] hi = 10;
  constraint c {
    x dist {
      3 :/ `W_LO,
      [lo + 1 : hi - 1] :/ `W_MID,
      10 :/ `W_HI
    };
  }
endclass

// The single-value items are non-constant.  This is the defect.
class VarItems;
  rand bit [3:0] x;
  bit [3:0] lo = 3;
  bit [3:0] hi = 10;
  constraint c {
    x dist {
      lo :/ `W_LO,
      [lo + 1 : hi - 1] :/ `W_MID,
      hi :/ `W_HI
    };
  }
endclass

// A 'rand' item is non-constant too, and is still a plain equality.
class RandItems;
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint cy {y inside {[1 : 2]};}
  constraint c {
    x dist {
      y :/ 90,
      9 :/ 10
    };
  }
endclass

// ':=' is a per-value weight (IEEE 1800-2023 18.5.3) rather than a weight spread
// across the range, so a non-literal single-value item has to be weighted the
// same as the literal spelling of it.  Values 0-9 carry weight 1 each and 'hi'
// carries weight 1, so x == 10 is expected 1 time in 11.
class ColonEqItems;
  rand bit [3:0] x;
  bit [3:0] hi = 10;
  constraint c {
    x dist {
      [0 : 9] := 1,
      hi := 1
    };
  }
endclass

module t;
  int nlo, nmid, nhi;
  int neqy, nnine;
  int nten;

  // One draw of x, bucketed by which part of the distribution it landed in.
  task automatic tally(input bit [3:0] x);
    `check_range(x, 3, 10)
    if (x == 3) nlo++;
    else if (x == 10) nhi++;
    else nmid++;
  endtask

  initial begin
    automatic LiteralItems li = new;
    automatic VarBounds vb = new;
    automatic VarItems vi = new;
    automatic RandItems ri = new;
    automatic ColonEqItems ce = new;

    nlo = 0;
    nmid = 0;
    nhi = 0;
    for (int i = 0; i < `N; i++) begin
      `checkd(li.randomize(), 1)
      tally(li.x);
    end
    `check_hist

    nlo = 0;
    nmid = 0;
    nhi = 0;
    for (int i = 0; i < `N; i++) begin
      `checkd(vb.randomize(), 1)
      tally(vb.x);
    end
    `check_hist

    nlo = 0;
    nmid = 0;
    nhi = 0;
    for (int i = 0; i < `N; i++) begin
      `checkd(vi.randomize(), 1)
      tally(vi.x);
    end
    `check_hist

    neqy = 0;
    nnine = 0;
    for (int i = 0; i < `N; i++) begin
      `checkd(ri.randomize(), 1)
      if (ri.x == 9) nnine++;
      else if (ri.x == ri.y) neqy++;
      else `stop;
    end
    `check_tol(neqy, `N * 90 / 100)
    `check_tol(nnine, `N * 10 / 100)

    nten = 0;
    for (int i = 0; i < `N; i++) begin
      `checkd(ce.randomize(), 1)
      // x is bit [3:0], so only the upper bound can fail
      if (ce.x > 10) `stop;
      if (ce.x == 10) nten++;
    end
    `check_tol(nten, `N / 11)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
