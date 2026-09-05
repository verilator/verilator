// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// Constraints with the same solution set must produce the same distribution.
// A constraint denotes a set of legal value combinations; nothing in IEEE 1800
// makes the distribution depend on which syntax was used to write that set
// down. Every assertion here is RELATIONAL - it compares two spellings of one
// solution space - so none of it depends on settling what the absolute rate
// ought to be.
//
// All six SameSpace* classes below describe exactly the same problem: a free
// `rand bit` guarding a pin of four 3-bit values, so one arm holds a single
// solution and the other holds 2**12. They differ only in spelling: explicit
// index, foreach, implication instead of if, queue, dynamic array, and four
// standalone scalars instead of four array elements.
//
// Five of the six agree closely on master, all sitting near 0/200 - which is
// what 18.5.10 uniformity requires, since the guarded arm is 1 of 4097
// solutions. The scalar spelling is the outlier at 97-108/200:
//
//   SameSpaceArrIdx    1-4      SameSpaceQueue     1-4
//   SameSpaceForeach   0-4      SameSpaceDyn       0-4
//   SameSpaceImpl      0-6      SameSpaceScalars  97-108   <-- disagrees
//
// So `foreach` is not the trigger and neither is the choice of `if` versus
// `->`; rewriting four array elements as four scalars of the same width moves
// the condition by a factor of thirty. Note which side is the anomaly: the
// array rows match the LRM and the scalar row does not. A fix must bring them
// into agreement, and 18.5.10 says it must do so by moving the SCALAR row down,
// not the array rows up. t_constraint_rand_cond_ok pins the array rows in place
// so that cannot silently happen the wrong way round.
//
// MultiBit is the same claim in a form that needs no cross-class comparison. A
// 2-bit condition with only mode 1 guarded leaves modes 0, 2 and 3 describing
// three arms of identical measure, so they must be equiprobable. Over 600
// solves master gives roughly 0:113  1:1  2:207  3:280 where the three
// unguarded modes should each be ~200. Mode 1 near zero is correct. The 2.5x
// spread among its three equal-measure siblings is not, and an absolute band
// would not catch it: 113 and 280 both sit inside a +/-5 sigma band around 200.
// That is the case for asserting relationally throughout this file.
//
// Nested versus conjoined guards are also compared. They agree on master; the
// row is kept so a fix cannot break the equivalence while repairing the rest.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_rel(label,ga,gb,tol) do begin $write("  %-46s %3d vs %3d  diff %3d (max %0d)  %s\n", label, (ga), (gb), ((ga)>(gb)?(ga)-(gb):(gb)-(ga)), (tol), ((((ga)>(gb)?(ga)-(gb):(gb)-(ga))) > (tol) ? "OUT-OF-BAND" : "ok")); if ((((ga)>(gb)?(ga)-(gb):(gb)-(ga))) > (tol)) bad++; end while(0);
// verilog_format: on

// Four pinned array elements, explicit index
class SameSpaceArrIdx;
  rand bit [2:0] a[4];
  rand bit sel;
  constraint c {
    if (sel) {
      a[0] == 3'd0;
      a[1] == 3'd0;
      a[2] == 3'd0;
      a[3] == 3'd0;
    }
  }
endclass

// Same set, foreach spelling
class SameSpaceForeach;
  rand bit [2:0] a[4];
  rand bit sel;
  constraint c {
    if (sel) {
      foreach (a[i]) a[i] == 3'd0;
    }
  }
endclass

// Same set, implication instead of if
class SameSpaceImpl;
  rand bit [2:0] a[4];
  rand bit sel;
  constraint c {
    sel -> {
      foreach (a[i]) a[i] == 3'd0;
    }
  }
endclass

// Same set, queue
class SameSpaceQueue;
  rand bit [2:0] q[$];
  rand bit sel;
  constraint c {
    q.size() == 4;
    if (sel) {foreach (q[i]) q[i] == 3'd0;}
  }
endclass

// Same set, dynamic array
class SameSpaceDyn;
  rand bit [2:0] d[];
  rand bit sel;
  constraint c {
    d.size() == 4;
    if (sel) {foreach (d[i]) d[i] == 3'd0;}
  }
endclass

// Same set, four standalone scalars instead of four array elements
class SameSpaceScalars;
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

// Nested guards
class NestedGuard;
  rand bit [2:0] a[4];
  rand bit s1, s2;
  constraint c {
    if (s1)
    if (s2) {
      foreach (a[i]) a[i] == 3'd0;
    }
  }
endclass

// Conjoined guard: extensionally identical to NestedGuard
class ConjoinedGuard;
  rand bit [2:0] a[4];
  rand bit s1, s2;
  constraint c {
    if (s1 && s2) {
      foreach (a[i]) a[i] == 3'd0;
    }
  }
endclass

// Multi-bit condition: modes 0, 2 and 3 are three arms of identical measure
class MultiBit;
  rand bit [2:0] a[8];
  rand bit [1:0] mode;
  constraint c {
    if (mode == 2'd1) {
      foreach (a[i]) a[i] == 3'd0;
    }
  }
endclass

module t;
  localparam int TRIALS = 200;
  // Two independent rows of a fair coin differ with sigma = sqrt(2)*7.07 = 10,
  // so 50 is 5 sigma. Rows that genuinely describe the same space cannot drift
  // past it, and the array-versus-scalar disagreement is about 100.
  localparam int REL_TOL = 50;

  // MultiBit needs more solves: the three equal-measure arms differ with
  // sigma = sqrt(600*2/3) = 20 at 600 trials. The assertion is on the SPREAD
  // across all three, max minus min, which is the natural statement and avoids
  // three separate pairwise checks sitting near their band edges. A tolerance
  // of 100 is 5 sigma; master's spread is about 185. At 200 trials the same
  // effect is only ~2.9 sigma, too close to the edge to assert safely.
  localparam int MTRIALS = 600;
  localparam int MODE_TOL = 100;

  SameSpaceArrIdx idx;
  SameSpaceForeach fe;
  SameSpaceImpl impl;
  SameSpaceQueue que;
  SameSpaceDyn dyn;
  SameSpaceScalars scl;
  NestedGuard nest;
  ConjoinedGuard conj;
  MultiBit mb;

  int n_idx, n_fe, n_impl, n_que, n_dyn, n_scl;
  int n_nest, n_conj;
  int mode_hist[4];
  int mode_lo;
  int mode_hi;
  int ok;
  int i;
  int bad;
  int viol;

  initial begin
    bad = 0;
    idx = new;
    fe = new;
    impl = new;
    que = new;
    dyn = new;
    scl = new;
    nest = new;
    conj = new;
    mb = new;

    n_idx = 0;
    viol = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = idx.randomize();
      `checkd(ok, 1)
      if (idx.sel) begin
        n_idx++;
        foreach (idx.a[j]) if (idx.a[j] != 3'd0) viol++;
      end
    end
    `checkd(viol, 0)

    n_fe = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = fe.randomize();
      `checkd(ok, 1)
      if (fe.sel) n_fe++;
    end

    n_impl = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = impl.randomize();
      `checkd(ok, 1)
      if (impl.sel) n_impl++;
    end

    n_que = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = que.randomize();
      `checkd(ok, 1)
      if (que.sel) n_que++;
    end

    n_dyn = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = dyn.randomize();
      `checkd(ok, 1)
      if (dyn.sel) n_dyn++;
    end

    n_scl = 0;
    viol = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = scl.randomize();
      `checkd(ok, 1)
      if (scl.sel) begin
        n_scl++;
        if (scl.s0 != 0 || scl.s1 != 0 || scl.s2 != 0 || scl.s3 != 0) viol++;
      end
    end
    `checkd(viol, 0)

    $write("one solution space, six spellings, %0d solves each:\n", TRIALS);
    $write("  ArrIdx %0d  Foreach %0d  Impl %0d  Queue %0d  Dyn %0d  Scalars %0d\n", n_idx, n_fe,
           n_impl, n_que, n_dyn, n_scl);
    `check_rel("ArrIdx vs Foreach  (foreach is not the trigger)", n_idx, n_fe, REL_TOL)
    `check_rel("ArrIdx vs Impl  (if vs ->)", n_idx, n_impl, REL_TOL)
    `check_rel("ArrIdx vs Queue", n_idx, n_que, REL_TOL)
    `check_rel("ArrIdx vs Dyn", n_idx, n_dyn, REL_TOL)
    `check_rel("ArrIdx vs Scalars  (array elems vs scalars)", n_idx, n_scl, REL_TOL)

    // Nested vs conjoined guards
    n_nest = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = nest.randomize();
      `checkd(ok, 1)
      if (nest.s1 && nest.s2) n_nest++;
    end
    n_conj = 0;
    for (i = 0; i < TRIALS; i++) begin
      ok = conj.randomize();
      `checkd(ok, 1)
      if (conj.s1 && conj.s2) n_conj++;
    end
    `check_rel("Nested vs Conjoined  (if(a) if(b) vs if(a&&b))", n_nest, n_conj, REL_TOL)

    // Multi-bit condition: modes 0, 2, 3 are equal-measure arms
    for (i = 0; i < 4; i++) mode_hist[i] = 0;
    for (i = 0; i < MTRIALS; i++) begin
      ok = mb.randomize();
      `checkd(ok, 1)
      mode_hist[mb.mode]++;
    end
    $write("multi-bit condition over %0d solves: 0:%0d 1:%0d 2:%0d 3:%0d\n", MTRIALS,
           mode_hist[0], mode_hist[1], mode_hist[2], mode_hist[3]);
    $write("  (mode 1 is the guarded arm and is correctly rare; 0, 2 and 3 have\n");
    $write("   identical measure and must be equiprobable)\n");
    mode_lo = mode_hist[0];
    mode_hi = mode_hist[0];
    if (mode_hist[2] < mode_lo) mode_lo = mode_hist[2];
    if (mode_hist[3] < mode_lo) mode_lo = mode_hist[3];
    if (mode_hist[2] > mode_hi) mode_hi = mode_hist[2];
    if (mode_hist[3] > mode_hi) mode_hi = mode_hist[3];
    `check_rel("MultiBit spread over equal-measure modes", mode_hi, mode_lo, MODE_TOL)

    if (bad != 0) begin
      $write("%%Error: %s:%0d: %0d relational check(s) failed\n", `__FILE__, `__LINE__, bad);
      $write("%%Error: A constraint denotes a set of legal value combinations. Two\n");
      $write("%%Error: constraints denoting the SAME set must randomize the same way,\n");
      $write("%%Error: whichever syntax spells them, and arms of equal measure must be\n");
      $write("%%Error: equiprobable.\n");
      `stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
