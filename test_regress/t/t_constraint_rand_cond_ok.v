// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// Behaviour in this area that is already CORRECT on master, pinned so it stays
// that way. This file passes today. Its companions - t_constraint_array_uniform,
// t_constraint_solve_before_lrm, t_constraint_rand_cond_skew and
// t_constraint_rand_cond_equiv - document what is broken.
//
// Two groups.
//
// GROUP 1: LRM-DIRECTION ROWS. IEEE 1800-2023 18.5.10 requires a uniform value
// distribution over legal value COMBINATIONS, not per-variable fairness. When a
// guarded arm holds one solution out of 2**24, the condition must be true
// almost never - the LRM's own worked example turns on exactly this point, and
// makes `solve ... before ...` the opt-in for anything else.
//
// These rows therefore assert that a rare arm STAYS rare. They are the guard
// against a well-meaning fix that makes every `rand` condition a 50/50 coin:
// that would look like fairness, would satisfy the skew tests, and would be
// wrong - it is the behaviour 18.5.10 explicitly describes as not happening,
// and no commercial simulator provides it.
//
// ScalarPin is the calibration row. One 3-bit variable pinned under the guard
// gives 9 solutions, one of which has the condition true, so 18.5.10 predicts
// 1/9 = 22/200. Master gives 17-30/200.
//
// GROUP 2: HARD SEMANTICS. Distribution heuristics must never override the
// language's guarantees. These are deterministic or near-deterministic and hold
// on master:
//
//   Randc      a `randc bit` condition cycles, so exactly 100 of 200 solves,
//              with no statistical width at all
//   Soft       a satisfiable `soft sel == 1` holds in all 200 solves even
//              though the guarded body is a hard pin over an array
//   Dist       `sel dist {0:=1, 1:=1}` asks for per-variable shaping explicitly
//              and gets it: 93-113/200, where the same class without the dist
//              sits at 1-4/200
//   ConstraintMode  constraint_mode(0) really disables the constraint - the
//              guarded pin stops being enforced
//   StateCond  a non-rand state variable as the condition still enforces the
//              guarded body when it is set
//
// The Dist row is worth keeping in view during any fix: it shows the solver can
// already deliver a shaped per-variable distribution when the user asks for one,
// which is the LRM-sanctioned way to get what the skew tests are asking for by
// accident.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_band(label,gotv,lov,hiv) do begin $write("  %-40s %3d/%0d  exp [%0d:%0d]  %s\n", label, (gotv), TRIALS, (lov), (hiv), (((gotv) < (lov) || (gotv) > (hiv)) ? "OUT-OF-BAND" : "ok")); if ((gotv) < (lov) || (gotv) > (hiv)) bad++; end while(0);
// verilog_format: on

// Guarded arm is 1 solution of 2**24 + 1
class ArrPin;
  rand bit [2:0] a[8];
  rand bit sel;
  constraint c {
    if (sel) {
      foreach (a[i]) a[i] == 3'd0;
    }
  }
endclass

// Both arms constrained, so neither is the trivial one
class ElseArm;
  rand bit [2:0] a[8];
  rand bit sel;
  constraint c {
    if (sel) {
      foreach (a[i]) a[i] == 3'd0;
    } else {
      foreach (a[i]) a[i] <= 3'd7;
    }
  }
endclass

// Two-dimensional array, same 24 bits
class Arr2D;
  rand bit [2:0] m[4][2];
  rand bit sel;
  constraint c {
    if (sel) {
      foreach (m[i]) foreach (m[i][j]) m[i][j] == 3'd0;
    }
  }
endclass

// Calibration: 9 solutions, 18.5.10 predicts 1/9
class ScalarPin;
  rand bit [2:0] a;
  rand bit sel;
  constraint c {
    if (sel) {
      a == 3'd0;
    }
  }
endclass

// randc condition must cycle regardless of any distribution heuristic
class RandcCond;
  rand bit [2:0] a[8];
  randc bit sel;
  constraint c {
    if (sel) {
      foreach (a[i]) a[i] == 3'd0;
    }
  }
endclass

// A satisfiable soft constraint must hold every time
class SoftCond;
  rand bit [2:0] a[8];
  rand bit sel;
  constraint c {
    if (sel) {
      foreach (a[i]) a[i] == 3'd0;
    }
    soft sel == 1;
  }
endclass

// dist asks for per-variable shaping explicitly
class DistCond;
  rand bit [2:0] a[8];
  rand bit sel;
  constraint c {
    if (sel) {
      foreach (a[i]) a[i] == 3'd0;
    }
    sel dist {
      0 := 1,
      1 := 1
    };
  }
endclass

// constraint_mode(0) must actually disable the constraint
class CmodeCond;
  rand bit [2:0] a[8];
  rand bit sel;
  constraint c {
    if (sel) {
      foreach (a[i]) a[i] == 3'd0;
    }
  }
endclass

// Non-rand state variable as the condition
class StateCond;
  rand bit [2:0] a[8];
  bit cfg;
  constraint c {
    if (cfg) {
      foreach (a[i]) a[i] == 3'd0;
    }
  }
endclass

module t;
  localparam int TRIALS = 200;
  // A rare arm must stay rare. A true rate of 2% clears 20/200 at about
  // 5 sigma, so this bound is not tight against master's 0-6.
  localparam int RARE_HI = 20;
  // ScalarPin: 18.5.10 predicts 22.2/200, sigma 4.44. [5,45] is +/-5 sigma.
  localparam int SCL_LO = 5;
  localparam int SCL_HI = 45;
  // Explicitly shaped by dist, so fair: [60,140] is +/-5.7 sigma.
  localparam int FAIR_LO = 60;
  localparam int FAIR_HI = 140;

  ArrPin arr_pin;
  ElseArm else_arm;
  Arr2D arr_2d;
  ScalarPin scalar_pin;
  RandcCond randc_cond;
  SoftCond soft_cond;
  DistCond dist_cond;
  CmodeCond cmode_cond;
  StateCond state_cond;

  int n;
  int ok;
  int i;
  int bad;
  int viol;

  initial begin
    bad = 0;
    $write("rows that are already correct, %0d solves each:\n", TRIALS);

    // ---- Group 1: LRM direction
    arr_pin = new;
    n = 0;
    viol = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = arr_pin.randomize();
      `checkd(ok, 1)
      if (arr_pin.sel) begin
        n++;
        foreach (arr_pin.a[j]) if (arr_pin.a[j] != 3'd0) viol++;
      end
    end
    `checkd(viol, 0)
    `check_band("ArrPin  (1 of 2**24+1 solutions)", n, 0, RARE_HI)

    else_arm = new;
    n = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = else_arm.randomize();
      `checkd(ok, 1)
      if (else_arm.sel) n++;
    end
    `check_band("ElseArm  (both arms constrained)", n, 0, RARE_HI)

    arr_2d = new;
    n = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = arr_2d.randomize();
      `checkd(ok, 1)
      if (arr_2d.sel) n++;
    end
    `check_band("Arr2D  (2-D array, same 24 bits)", n, 0, RARE_HI)

    scalar_pin = new;
    n = 0;
    viol = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = scalar_pin.randomize();
      `checkd(ok, 1)
      if (scalar_pin.sel) begin
        n++;
        if (scalar_pin.a != 3'd0) viol++;
      end
    end
    `checkd(viol, 0)
    `check_band("ScalarPin  (18.5.10 predicts 1/9 = 22)", n, SCL_LO, SCL_HI)

    // ---- Group 2: hard semantics
    randc_cond = new;
    n = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = randc_cond.randomize();
      `checkd(ok, 1)
      if (randc_cond.sel) n++;
    end
    // randc over a 1-bit variable cycles: exactly half, no statistical width
    `check_band("RandcCond  (randc cycles, exact)", n, TRIALS / 2, TRIALS / 2)

    soft_cond = new;
    n = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = soft_cond.randomize();
      `checkd(ok, 1)
      if (soft_cond.sel) n++;
    end
    // The soft is satisfiable in every solve, so it must hold in every solve
    `check_band("SoftCond  (satisfiable soft, exact)", n, TRIALS, TRIALS)

    dist_cond = new;
    n = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = dist_cond.randomize();
      `checkd(ok, 1)
      if (dist_cond.sel) n++;
    end
    `check_band("DistCond  (sel dist {0:=1,1:=1})", n, FAIR_LO, FAIR_HI)

    // constraint_mode(0) must really disable the constraint: with it off the
    // guarded pin has to stop being enforced.
    cmode_cond = new;
    cmode_cond.c.constraint_mode(0);
    n = 0;
    viol = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = cmode_cond.randomize();
      `checkd(ok, 1)
      if (cmode_cond.sel) begin
        n++;
        foreach (cmode_cond.a[j]) if (cmode_cond.a[j] != 3'd0) viol++;
      end
    end
    $write("  %-40s sel==1 %3d/%0d, pin violated %0d times\n", "CmodeCond  (constraint_mode(0))",
           n, TRIALS, viol);
    if (n > 0 && viol == 0) begin
      $write("%%Error: %s:%0d: constraint_mode(0) did not disable the constraint\n", `__FILE__,
             `__LINE__);
      bad++;
    end

    // Non-rand state variable as the condition: the body must be enforced
    state_cond = new;
    state_cond.cfg = 1'b1;
    viol = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = state_cond.randomize();
      `checkd(ok, 1)
      foreach (state_cond.a[j]) if (state_cond.a[j] != 3'd0) viol++;
    end
    `checkd(viol, 0)
    $write("  %-40s guarded body enforced\n", "StateCond  (non-rand condition)");

    if (bad != 0) begin
      $write("%%Error: %s:%0d: %0d row(s) regressed\n", `__FILE__, `__LINE__, bad);
      $write("%%Error: These rows are correct on master. A rare arm must stay rare:\n");
      $write("%%Error: IEEE 1800-2023 18.5.10 requires uniformity over legal value\n");
      $write("%%Error: COMBINATIONS, not per-variable fairness, and makes solve..before\n");
      $write("%%Error: the opt-in for anything else. Hard semantics - randc, soft, dist,\n");
      $write("%%Error: constraint_mode - must outrank any distribution heuristic.\n");
      `stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
