// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// `solve ... before ...` does the OPPOSITE of what IEEE 1800-2023 18.5.10
// specifies, on the worked example the standard itself uses to define the
// construct.
//
// The LRM's example, reproduced verbatim in class LrmPlain below:
//
//   class B;
//     rand bit s;
//     rand bit [31:0] d;
//     constraint c { s -> d == 0; }
//   endclass
//
// There are 2**32 + 1 solutions: 2**32 with s == 0 and any d, and exactly one
// with s == 1 and d == 0. Under 18.5.10's uniformity requirement s must
// therefore be 0 with probability 2**32/(2**32 + 1), i.e. s == 1 essentially
// never. The LRM presents this skew as the CORRECT result, and presents
// `solve s before d` as the user's opt-in to make s a fair coin:
// "the same 2**32+1 solutions can be produced, but with different probability".
//
// Both halves come out backwards on master, over 8 seeds x 200 solves:
//
//                                  LRM     master
//   LrmPlain    (no ordering)      ~0      90-112     far too HIGH
//   LrmSolved   (solve s before d) ~100    0          far too LOW
//
// The construct is not merely weak here, it is inverted: without it the rare
// arm is taken half the time, and adding it removes the rare arm completely.
// `randomize()` returns 1 on every one of those solves, so this is not a
// silent solver failure - the values really are being chosen this way.
//
// SolveCondFirst is the same claim on the array shape that motivated this
// suite: `solve sel before a` is specified to make sel's distribution
// independent of the constraint it guards, so sel should be ~100/200. Master
// gives 41-57/200. It is printed but NOT asserted - master lands just under any
// band wide enough to survive an RNG-stream reshuffle, and the LrmPlain /
// LrmSolved pair already makes the point decisively.
//
// Mechanism, for whoever fixes this: in the phased path the per-phase diversity
// constraint (verilated_random.cpp solvePhaseValues) calls randomConstraint,
// which XORs bits drawn from ALL of m_vars - including the variables in later
// solve layers - into the check that decides the current layer's values. The
// ordering machinery re-couples the condition to the very variables it was
// asked to be solved before.
//
// SolveArrFirst is deliberately asserted loosely. `solve a before sel` picks
// the 24-bit array first, after which all-elements-zero is essentially
// impossible, so sel should be ~0. Master gives 12-26/200, which is also too
// high, but the LRM text supports projection-uniformity for the first-solved
// variable less quotably than it supports the two rows above, so this row is
// held to a one-sided sanity bound rather than made the point of the test.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_band(label,gotv,lov,hiv) do begin $write("  %-38s cond true %3d/%0d  exp [%0d:%0d]  %s\n", label, (gotv), TRIALS, (lov), (hiv), (((gotv) < (lov) || (gotv) > (hiv)) ? "OUT-OF-BAND" : "ok")); if ((gotv) < (lov) || (gotv) > (hiv)) bad++; end while(0);
// verilog_format: on

// IEEE 1800-2023 18.5.10, verbatim. s == 1 should be vanishingly rare.
class LrmPlain;
  rand bit s;
  rand bit [31:0] d;
  constraint c {s -> d == 0;}
endclass

// The same, with the ordering the LRM says makes s a fair coin.
class LrmSolved;
  rand bit s;
  rand bit [31:0] d;
  constraint c {s -> d == 0;}
  constraint o {solve s before d;}
endclass

// Same claim, array shape: ordering must decouple sel from what it guards.
class SolveCondFirst;
  rand bit [2:0] a[8];
  rand bit sel;
  constraint c {
    if (sel) {
      foreach (a[i]) a[i] == 3'd0;
    }
  }
  constraint o {solve sel before a;}
endclass

// Opposite ordering: array first, so the condition should almost never hold.
class SolveArrFirst;
  rand bit [2:0] a[8];
  rand bit sel;
  constraint c {
    if (sel) {
      foreach (a[i]) a[i] == 3'd0;
    }
  }
  constraint o {solve a before sel;}
endclass

module t;
  // Binomial(200, 0.5): mean 100, sigma 7.07, so [60,140] is +/-5.7 sigma.
  // A one-sided <=20 bound corresponds to a true rate of 2% at about 5 sigma.
  localparam int TRIALS = 200;
  localparam int FAIR_LO = 60;
  localparam int FAIR_HI = 140;
  localparam int RARE_HI = 20;
  // SolveArrFirst: loose one-sided sanity bound, see header.
  localparam int LOOSE_HI = 40;

  LrmPlain lrm_plain;
  LrmSolved lrm_solved;
  SolveCondFirst cond_first;
  SolveArrFirst arr_first;

  int n;
  int ok;
  int i;
  int bad;
  int viol;

  initial begin
    bad = 0;
    $write("IEEE 1800-2023 18.5.10 solve..before, %0d solves per row:\n", TRIALS);

    // No ordering: 2**32+1 solutions, only one of which has s == 1.
    lrm_plain = new;
    n = 0;
    viol = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = lrm_plain.randomize();
      `checkd(ok, 1)
      if (lrm_plain.s) begin
        n++;
        if (lrm_plain.d != 32'd0) viol++;
      end
    end
    // The implication itself must hold whenever s was chosen true.
    `checkd(viol, 0)
    `check_band("LrmPlain  (s -> d==0, no ordering)", n, 0, RARE_HI)

    // With `solve s before d` the LRM says s becomes a fair coin.
    lrm_solved = new;
    n = 0;
    viol = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = lrm_solved.randomize();
      `checkd(ok, 1)
      if (lrm_solved.s) begin
        n++;
        if (lrm_solved.d != 32'd0) viol++;
      end
    end
    `checkd(viol, 0)
    `check_band("LrmSolved  (solve s before d)", n, FAIR_LO, FAIR_HI)

    // Array shape: ordering must decouple the condition from what it guards.
    cond_first = new;
    n = 0;
    viol = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = cond_first.randomize();
      `checkd(ok, 1)
      if (cond_first.sel) begin
        n++;
        foreach (cond_first.a[j]) if (cond_first.a[j] != 3'd0) viol++;
      end
    end
    `checkd(viol, 0)
    // Informational, not asserted. `solve sel before a` should decouple sel and
    // put this at ~100/200; master gives 41-57. The claim is sound but master
    // lands just under any band wide enough to be safe against an RNG-stream
    // reshuffle, so asserting it would buy a flaky test for a point the
    // LrmPlain/LrmSolved pair above already makes decisively.
    $write("  %-38s cond true %3d/%0d  (should be ~%0d, informational)\n",
           "SolveCondFirst  (solve sel before a)", n, TRIALS, TRIALS / 2);

    // Opposite ordering: loose one-sided bound only, see header.
    arr_first = new;
    n = 0;
    viol = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = arr_first.randomize();
      `checkd(ok, 1)
      if (arr_first.sel) begin
        n++;
        foreach (arr_first.a[j]) if (arr_first.a[j] != 3'd0) viol++;
      end
    end
    `checkd(viol, 0)
    `check_band("SolveArrFirst  (solve a before sel)", n, 0, LOOSE_HI)

    if (bad != 0) begin
      $write("%%Error: %s:%0d: %0d row(s) outside band\n", `__FILE__, `__LINE__, bad);
      $write("%%Error: IEEE 1800-2023 18.5.10 defines solve..before on exactly the\n");
      $write("%%Error: LrmPlain/LrmSolved pair: without ordering the one-solution arm\n");
      $write("%%Error: is essentially never taken, and `solve s before d` makes the\n");
      $write("%%Error: condition a fair coin. Master inverts both halves.\n");
      `stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
