// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// A `rand` variable used as a constraint condition is driven to a badly skewed
// value once a rand ARRAY is present in the same randomize(). This is the
// guard-visible symptom of the value-distribution defect documented in
// t_constraint_array_uniform; that file is the root cause and the better place
// to start.
//
// Three independent shapes, all failing on master over 8 seeds x 200 solves.
//
// 1. VACUOUS GUARD BODY. `a` is bit [2:0], so `a[i] <= 3'd7` is true for every
//    value it can hold. Both arms of the `if` mean exactly the same thing and
//    `sel` is a free coin flip under any model whatsoever. Master: 159-182/200.
//    The literal, runtime-bound and `inside` spellings all behave alike, which
//    rules out constant folding as the explanation.
//
// 2. CONTAMINATION BY AN UNRELATED ARRAY. VacBase pins four scalars under the
//    guard and contains no array at all; it is fair at 85-108/200. Adding
//    `foreach (pad[i]) pad[i] <= 3'd7` - a constraint that excludes nothing and
//    never mentions `sel` - drops the same guard to 21-33/200. The constraint
//    system factorizes into independent components, so sel's marginal cannot
//    legally depend on a vacuous constraint over a disjoint variable.
//
//    CtlUnusedArr is the discriminating control: it has the same array member
//    but leaves it UNCONSTRAINED, so the array never enters the solver, and the
//    guard stays fair. What matters is not that the class declares an array,
//    but that an array is pulled into the solver problem - which switches the
//    whole object onto solveDiversityXor (verilated_random.cpp:633-646).
//
// 3. OVER-SELECTION OF A RESTRICTIVE ARM. `a[i] inside {[0:4]}` admits 5**8 of
//    8**8 combinations, so 18.5.10 uniformity puts the guard true about 2.3% of
//    the time, i.e. ~5/200. Master gives 146-167/200. Note this runs OPPOSITE
//    to the pinned-guard rows in t_constraint_rand_cond_ok, which sit near 0
//    exactly as the LRM requires. The skew has no consistent direction, so a
//    fix may not simply push conditions one way.
//
// CtlScalarVacuous is the positive control throughout: the same vacuous guard
// over a scalar takes the bit-pinning path and is fair at 89-110/200. It must
// stay fair after any fix.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_band(label,gotv,lov,hiv) do begin $write("  %-40s sel==1 %3d/%0d  exp [%0d:%0d]  %s\n", label, (gotv), TRIALS, (lov), (hiv), (((gotv) < (lov) || (gotv) > (hiv)) ? "OUT-OF-BAND" : "ok")); if ((gotv) < (lov) || (gotv) > (hiv)) bad++; end while(0);
`define check_rel(label,ga,gb,tol) do begin $write("  %-40s %3d vs %3d  diff %3d (max %0d)  %s\n", label, (ga), (gb), ((ga)>(gb)?(ga)-(gb):(gb)-(ga)), (tol), ((((ga)>(gb)?(ga)-(gb):(gb)-(ga))) > (tol) ? "OUT-OF-BAND" : "ok")); if ((((ga)>(gb)?(ga)-(gb):(gb)-(ga))) > (tol)) bad++; end while(0);
// verilog_format: on

// 1. Vacuous guarded body, literal bound
class VacLiteral;
  rand bit [2:0] a[8];
  rand bit sel;
  constraint c {
    if (sel) {
      foreach (a[i]) a[i] <= 3'd7;
    }
  }
endclass

// 1. Vacuous guarded body, runtime bound so it cannot be folded away
class VacRuntime;
  rand bit [2:0] a[8];
  rand bit sel;
  bit [2:0] lim;
  constraint c {
    if (sel) {
      foreach (a[i]) a[i] <= lim;
    }
  }
endclass

// 1. Vacuous guarded body, `inside` covering the whole type range
class VacInside;
  rand bit [2:0] a[8];
  rand bit sel;
  constraint c {
    if (sel) {
      foreach (a[i]) a[i] inside {[3'd0 : 3'd7]};
    }
  }
endclass

// 2. Baseline: four pinned scalars under the guard, no array anywhere
class VacBase;
  rand bit [2:0] s0, s1, s2, s3;
  rand bit sel;
  constraint c {
    if (sel) {
      s0 == 3'd0;
      s1 == 3'd0;
      s2 == 3'd0;
      s3 == 3'd0;
    }
  }
endclass

// 2. Identical, plus a vacuous constraint on an array disjoint from the guard
class VacBasePlusArr;
  rand bit [2:0] s0, s1, s2, s3;
  rand bit sel;
  rand bit [2:0] pad[4];
  constraint c {
    if (sel) {
      s0 == 3'd0;
      s1 == 3'd0;
      s2 == 3'd0;
      s3 == 3'd0;
    }
    foreach (pad[i]) pad[i] <= 3'd7;
  }
endclass

// 2. Control: same array member, but UNCONSTRAINED so it never enters the
// solver. Fair, and must stay fair.
class CtlUnusedArr;
  rand bit [2:0] s0, s1, s2, s3;
  rand bit sel;
  rand bit [2:0] pad[4];
  constraint c {
    if (sel) {
      s0 == 3'd0;
      s1 == 3'd0;
      s2 == 3'd0;
      s3 == 3'd0;
    }
  }
endclass

// 3. Restrictive arm, admitting 5**8 of 8**8 combinations
class RestrictedArm;
  rand bit [2:0] a[8];
  rand bit sel;
  constraint c {
    if (sel) {
      foreach (a[i]) a[i] inside {[3'd0 : 3'd4]};
    }
  }
endclass

// Control: vacuous guard over a scalar. Bit-pinning path. Fair.
class CtlScalarVacuous;
  rand bit [2:0] a;
  rand bit sel;
  constraint c {
    if (sel) {
      a <= 3'd7;
    }
  }
endclass

module t;
  // Binomial(200, 0.5): mean 100, sigma 7.07, so [60,140] is +/-5.7 sigma.
  localparam int TRIALS = 200;
  localparam int FAIR_LO = 60;
  localparam int FAIR_HI = 140;
  // Two independent fair rows differ with sigma = sqrt(2)*7.07 = 10, so a
  // tolerance of 40 on the difference is 4 sigma - wide enough that two rows
  // which really are fair cannot trip it, and master's 67 clears it by 27.
  localparam int REL_TOL = 40;
  // 18.5.10 puts RestrictedArm near 5/200; 40 is a deliberately generous
  // one-sided bound that master still misses by a factor of four.
  localparam int RESTRICT_HI = 40;

  VacLiteral vac_lit;
  VacRuntime vac_rt;
  VacInside vac_ins;
  VacBase vac_base;
  VacBasePlusArr vac_arr;
  CtlUnusedArr ctl_unused;
  RestrictedArm restricted;
  CtlScalarVacuous ctl_scl;

  int n_base;
  int n_arr;
  int n_unused;
  int n;
  int ok;
  int i;
  int bad;

  initial begin
    bad = 0;
    $write("condition-true rate per shape, %0d solves each:\n", TRIALS);

    // ---- 1. vacuous guarded body over an array
    vac_lit = new;
    n = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = vac_lit.randomize();
      `checkd(ok, 1)
      if (vac_lit.sel) n++;
    end
    `check_band("VacLiteral  (a[i] <= 3'd7)", n, FAIR_LO, FAIR_HI)

    vac_rt = new;
    vac_rt.lim = 3'd7;
    n = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = vac_rt.randomize();
      `checkd(ok, 1)
      if (vac_rt.sel) n++;
    end
    `check_band("VacRuntime  (a[i] <= lim, lim==7)", n, FAIR_LO, FAIR_HI)

    vac_ins = new;
    n = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = vac_ins.randomize();
      `checkd(ok, 1)
      if (vac_ins.sel) n++;
    end
    `check_band("VacInside  (a[i] inside [0:7])", n, FAIR_LO, FAIR_HI)

    // ---- 2. contamination by an unrelated, vacuously constrained array
    vac_base = new;
    n_base = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = vac_base.randomize();
      `checkd(ok, 1)
      if (vac_base.sel) n_base++;
    end
    `check_band("VacBase  (4 pinned scalars, no array)", n_base, FAIR_LO, FAIR_HI)

    vac_arr = new;
    n_arr = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = vac_arr.randomize();
      `checkd(ok, 1)
      if (vac_arr.sel) n_arr++;
    end
    $write("  %-40s sel==1 %3d/%0d\n", "VacBasePlusArr  (+ vacuous array)", n_arr, TRIALS);

    ctl_unused = new;
    n_unused = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = ctl_unused.randomize();
      `checkd(ok, 1)
      if (ctl_unused.sel) n_unused++;
    end
    $write("  %-40s sel==1 %3d/%0d\n", "CtlUnusedArr  (array unconstrained)", n_unused, TRIALS);

    // Adding a vacuous constraint over a disjoint array must not move the guard
    `check_rel("VacBase vs VacBasePlusArr", n_base, n_arr, REL_TOL)
    // Control: the same array left unconstrained must not move it either
    `check_rel("VacBase vs CtlUnusedArr", n_base, n_unused, REL_TOL)

    // ---- 3. restrictive arm over-selected
    restricted = new;
    n = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = restricted.randomize();
      `checkd(ok, 1)
      if (restricted.sel) n++;
    end
    `check_band("RestrictedArm  (a[i] inside [0:4])", n, 0, RESTRICT_HI)

    // ---- control
    ctl_scl = new;
    n = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = ctl_scl.randomize();
      `checkd(ok, 1)
      if (ctl_scl.sel) n++;
    end
    `check_band("CtlScalarVacuous  (control, scalar)", n, FAIR_LO, FAIR_HI)

    if (bad != 0) begin
      $write("%%Error: %s:%0d: %0d row(s) outside band\n", `__FILE__, `__LINE__, bad);
      $write("%%Error: A guarded body that excludes no value leaves both arms of the\n");
      $write("%%Error: `if` semantically identical, so the condition must be a fair\n");
      $write("%%Error: coin; and a vacuous constraint over a variable disjoint from\n");
      $write("%%Error: the condition cannot legally change the condition's marginal.\n");
      `stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
