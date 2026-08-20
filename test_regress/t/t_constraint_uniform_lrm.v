// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 18.5.9 (18.5.10 in 1800-2017) requires that the solver
// "assure that the random values are selected to give a uniform value
// distribution over legal value combinations (that is, all combinations of
// legal values have the same probability of being the solution)".
//
// This is the worked example from that clause.  There are 1 + 2**8 legal
// {s,d} combinations and s is true in only one of them, so Table 18-1 of the
// clause gives every combination probability 1/257, and s is set in about one
// draw in 257.
//
// The runtime sets s about half the time instead, which is roughly the
// Table 18-2 distribution that the clause reserves for "solve s before d".
//
// The second half of this test runs the ordered form for contrast, but only
// prints what it sees rather than checking it.  That form does not match
// Table 18-2 either -- it comes out near 27% rather than 50% -- but it takes
// a different path through the runtime (the phased solve rather than the
// per-bit pinning), so it looks like a separate matter and is left out of the
// pass criterion here.  See issue #8024.

// verilog_format: off
`define stop $stop
`define check_range(nam,gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d: %s: got=%0d exp=%0d..%0d\n", `__FILE__,`__LINE__, nam, (gotv), (minv), (maxv)); fails++; end while(0);
// verilog_format: on

`define N 2000

// The class exactly as printed in IEEE 1800-2023 18.5.9.
class B;
  rand bit s;
  rand bit [7:0] d;
  constraint c {s -> d == 0;}
endclass

// The same class with the ordering the clause uses to obtain Table 18-2.
class BOrdered;
  rand bit s;
  rand bit [7:0] d;
  constraint c {s -> d == 0;}
  constraint order {solve s before d;}
endclass

module t;
  int fails;

  initial begin
    automatic B b = new;
    automatic BOrdered bo = new;
    int s_ones;
    int s_ones_ordered;
    int i;
    int r;

    // Table 18-1: no ordering, so every legal {s,d} pair is equally likely
    // and s is set in 1 of 257 draws.  Binomial(`N, 1/257) has mean 7.8 and
    // standard deviation 2.8, so the upper bound below sits about 11 sigma
    // out and a uniform solver passes with room to spare.
    for (i = 0; i < `N; i++) begin
      r = b.randomize();
      `check_range("randomize", r, 1, 1)
      if (b.s) s_ones++;
    end
    $display("Table 18-1  s==1 in %0d/%0d draws (expected about %0d)", s_ones, `N, `N / 257);
    `check_range("s==1 without solve-before", s_ones, 0, 40)

    // Table 18-2: "solve s before d" picks s first, so the clause puts s at
    // 50%.  Reported for contrast only; see the note at the top of the file.
    for (i = 0; i < `N; i++) begin
      r = bo.randomize();
      `check_range("randomize ordered", r, 1, 1)
      if (bo.s) s_ones_ordered++;
    end
    $display("Table 18-2  s==1 in %0d/%0d draws (expected about %0d, not checked here)",
             s_ones_ordered, `N, `N / 2);

    if (fails != 0) begin
      $write("%%Error: %0d check(s) outside tolerance\n", fails);
      `stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
