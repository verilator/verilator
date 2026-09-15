// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// A `rand` ARRAY solved through the constraint solver takes grossly non-uniform
// values, even when the only constraint on it is vacuous.
//
//   class C;
//     rand bit [2:0] a[8];
//     constraint c { foreach (a[i]) a[i] <= 3'd7; }
//   endclass
//
// `a` is `bit [2:0]`, so its largest possible value IS 7 and `a[i] <= 3'd7` is
// true for every value the type can hold. The constraint excludes nothing, so
// the eight values 0..7 must be equally likely. Over 800 solves x 8 elements =
// 6400 samples, uniform is 800 per value. Master produces roughly:
//
//   value  0     1     2    3    4     5    6    7
//   count  2133  1591  187  129  1647  529  143  41
//
// a 52x spread between the most and least likely value, and stable to within a
// few percent across seeds - a systematic bias, not sampling noise.
//
// IEEE 1800-2023 18.5.10 requires the solver to "assure that the random values
// are selected to give a uniform value distribution over legal value
// combinations". No reading of that sentence permits value 7 to be 20x rarer
// than value 0 under a constraint that excludes nothing.
//
// Two controls localise it to the solver's ARRAY path:
//
//   CtlArrNoConstraint  the same array with NO constraint at all. It never
//                       enters the solver and is uniform (752-838 per bucket).
//   CtlScalarVacuous    the same vacuous constraint on a SCALAR. It takes the
//                       bit-pinning path (verilated_random.cpp
//                       solveDiversityPins) and is uniform (85-112 of 800).
//
// The failing rows take solveDiversityXor instead, which verilated_random.cpp
// selects per-OBJECT whenever any solver variable has dimension > 0 (see
// verilated_random.cpp:633-646). Note the selector is per-object, not
// per-variable: one array member drags every other variable in the same
// randomize() onto the XOR path.
//
// ArrRestricted shows this is not limited to vacuous constraints. Under
// `a[i] < 3'd6` the excluded values 6 and 7 are correctly absent - the hard
// constraint is honoured - but the six legal values spread 143..2094 where each
// should be about 1067.
//
// This is the root defect. The guard-condition skew documented in
// t_constraint_rand_cond_skew is a downstream symptom of it.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Vacuous constraint over 8 elements. FAILING on master.
class ArrVacuous;
  rand bit [2:0] a[8];
  constraint c {
    foreach (a[i]) a[i] <= 3'd7;
  }
endclass

// Genuinely restrictive, but still six legal values per element.
// The exclusion is honoured; the distribution over what remains is not.
class ArrRestricted;
  rand bit [2:0] a[8];
  constraint c {
    foreach (a[i]) a[i] < 3'd6;
  }
endclass

// Control: no constraint at all, so the array bypasses the solver. Uniform.
class CtlArrNoConstraint;
  rand bit [2:0] a[8];
endclass

// Control: same vacuous constraint on a scalar. Bit-pinning path. Uniform.
class CtlScalarVacuous;
  rand bit [2:0] a;
  constraint c {a <= 3'd7;}
endclass

module t;
  // 800 solves. For the 8-element arrays that is 6400 samples over 8 values,
  // so uniform is 800 per value with sigma = sqrt(6400*(1/8)*(7/8)) = 26.5.
  // The +/-25% band [600,1000] is +/-7.5 sigma: a uniform mechanism escapes it
  // with probability far below 1e-12, while master misses it on six of the
  // eight buckets.
  localparam int SOLVES = 800;
  localparam int NELEM = 8;
  localparam int NVAL = 8;
  localparam int ARR_SAMPLES = SOLVES * NELEM;
  localparam int ARR_EXP = ARR_SAMPLES / NVAL;  // 800
  localparam int ARR_LO = (ARR_EXP * 3) / 4;  // 600
  localparam int ARR_HI = (ARR_EXP * 5) / 4;  // 1000

  // Restricted case: 6400 samples over 6 legal values, expected 1066.
  localparam int RES_NVAL = 6;
  localparam int RES_EXP = ARR_SAMPLES / RES_NVAL;
  localparam int RES_LO = (RES_EXP * 3) / 4;
  localparam int RES_HI = (RES_EXP * 5) / 4;

  // Scalar control: 800 samples over 8 values, expected 100, sigma 9.35.
  // [60,140] is +/-4.3 sigma.
  localparam int SCL_LO = 60;
  localparam int SCL_HI = 140;

  ArrVacuous arr_vac;
  ArrRestricted arr_res;
  CtlArrNoConstraint ctl_none;
  CtlScalarVacuous ctl_scl;

  int h[8];
  int i;
  int j;
  int ok;
  int bad;
  int viol;

  // Print a histogram and count how many buckets fall outside [lo,hi]
  function automatic int band_check(string label, int hh[8], int lo, int hi, int nval);
    int outside = 0;
    $write("  %-22s", label);
    for (int k = 0; k < 8; k++) $write(" %5d", hh[k]);
    for (int k = 0; k < nval; k++) if (hh[k] < lo || hh[k] > hi) outside++;
    $write("   band [%0d:%0d] outside=%0d %s\n", lo, hi, outside,
           (outside != 0) ? "OUT-OF-BAND" : "ok");
    return outside;
  endfunction

  initial begin
    bad = 0;
    arr_vac = new;
    arr_res = new;
    ctl_none = new;
    ctl_scl = new;

    $write("value histograms over %0d solves (uniform = equal buckets):\n", SOLVES);
    $write("  %-22s %5s %5s %5s %5s %5s %5s %5s %5s\n", "shape", "0", "1", "2", "3", "4", "5",
           "6", "7");

    // Vacuous constraint over an array. Every value 0..7 is legal.
    for (j = 0; j < 8; j++) h[j] = 0;
    for (i = 0; i < SOLVES; i++) begin
      ok = arr_vac.randomize();
      `checkd(ok, 1)
      foreach (arr_vac.a[k]) h[arr_vac.a[k]]++;
    end
    bad += band_check("ArrVacuous", h, ARR_LO, ARR_HI, NVAL);

    // Restricted: 6 and 7 must never appear, 0..5 must be near-equal.
    for (j = 0; j < 8; j++) h[j] = 0;
    viol = 0;
    for (i = 0; i < SOLVES; i++) begin
      ok = arr_res.randomize();
      `checkd(ok, 1)
      foreach (arr_res.a[k]) begin
        h[arr_res.a[k]]++;
        if (arr_res.a[k] >= 3'd6) viol++;
      end
    end
    // The hard constraint itself must hold; only the distribution is at issue.
    `checkd(viol, 0)
    bad += band_check("ArrRestricted (<6)", h, RES_LO, RES_HI, RES_NVAL);

    // Control: unconstrained array bypasses the solver.
    for (j = 0; j < 8; j++) h[j] = 0;
    for (i = 0; i < SOLVES; i++) begin
      ok = ctl_none.randomize();
      `checkd(ok, 1)
      foreach (ctl_none.a[k]) h[ctl_none.a[k]]++;
    end
    bad += band_check("CtlArrNoConstraint", h, ARR_LO, ARR_HI, NVAL);

    // Control: same vacuous constraint on a scalar, bit-pinning path.
    for (j = 0; j < 8; j++) h[j] = 0;
    for (i = 0; i < SOLVES; i++) begin
      ok = ctl_scl.randomize();
      `checkd(ok, 1)
      h[ctl_scl.a]++;
    end
    bad += band_check("CtlScalarVacuous", h, SCL_LO, SCL_HI, NVAL);

    if (bad != 0) begin
      $write("%%Error: %s:%0d: %0d value bucket(s) outside band\n", `__FILE__, `__LINE__, bad);
      $write("%%Error: IEEE 1800-2023 18.5.10: the solver shall give a uniform value\n");
      $write("%%Error: distribution over legal value combinations. A constraint that\n");
      $write("%%Error: excludes no value must leave every value equally likely.\n");
      `stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
