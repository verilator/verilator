// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// A 'dist' constrains a value to the union of its items and weights the choice
// among them (IEEE 1800-2023 18.5.4), identically whether written at class
// scope or in an inline randomize() with {} clause (18.7).
//
// Groups: A weight operators, B weight expressions, C items and bounds,
// D call forms, E structural contexts, F class-scope interaction, G enums and
// array bounds and rand_mode, H methods and inheritance, I every bucket of one
// distribution, J the bucket choice yielding to a hard constraint.
//
// Each check reports on its own and the run stops at the end, so one run
// prints every failure rather than the first.

// verilog_format: off
`define stop $stop
`define chk(NAME, CALL, PRED, LO, HI) \
  cnt = 0; nok = 0; \
  for (int i = 0; i < `N; i++) begin \
    ok = CALL; \
    if (ok != 0) begin nok++; if (PRED) cnt++; end \
  end \
  report(NAME, cnt, LO, HI, nok, `N);
// verilog_format: on

`define N 200

class Holder;
  rand bit [1:0] v;
endclass

class Holder3;
  rand bit [2:0] v;
endclass

class HolderInt;
  rand int x;
endclass

class HolderWide;
  rand bit [39:0] x;
endclass

class MemberWeight;
  rand bit [1:0] v;
  int wa, wb;
endclass

class QHolder;
  rand bit [3:0] v;
  bit [3:0] que[$];
endclass

class ArrHolder;
  rand bit [2:0] a[4];
endclass

class Inner;
  rand bit [1:0] v;
endclass

class Outer;
  rand Inner inn;
  function new();
    inn = new;
  endfunction
endclass

class TwoVar;
  rand bit [1:0] v;
  rand bit [1:0] w;
endclass

// Class-scope constraint on a *different* variable than the inline dist.
class SideConstraint;
  rand bit [1:0] v;
  rand bit [3:0] w;
  constraint cw {w > 4'd9;}
endclass

// Class-scope non-dist constraint on the *same* variable as the inline dist.
class NarrowConstraint;
  rand bit [1:0] v;
  constraint cv {v <= 2'd1;}
endclass

// Non-zero-based, descending unpacked array bounds.
class NegIdxArr;
  rand bit [2:0] a[5:-2];
endclass

typedef enum bit [1:0] {
  OP_RD,
  OP_WR,
  OP_NOP,
  OP_RSV
} op_e;

class OpHolder;
  rand op_e op;
endclass

// A variable frozen with rand_mode(0) keeps its value across randomize().
class ModeHolder;
  rand bit [1:0] v;
  rand bit [1:0] w;
endclass

// A randomize() with clause written inside a class method, the shape a UVM
// sequence body() uses, resolving a weight from a member and from a local.
class Seq;
  rand bit [1:0] v;
  int mw = 90;
  function int go_member();
    return this.randomize() with {
      v dist {
        0 :/ mw,
        1 :/ 10
      };
    };
  endfunction
  function int go_local();
    automatic int q = 90;
    return this.randomize() with {
      v dist {
        0 :/ q,
        1 :/ 10
      };
    };
  endfunction
endclass

// An inline dist on a member declared in a base class.
class DistBase;
  rand bit [1:0] v;
endclass

class DistDerived extends DistBase;
  rand bit [1:0] w;
endclass

// The same four-bucket distribution at class scope, as a control for the
// inline histogram below.
class HistClassScope;
  rand bit [1:0] v;
  constraint c {
    v dist {
      0 :/ 70,
      1 :/ 10,
      2 :/ 10,
      3 :/ 10
    };
  }
endclass

// Heavy bucket is a single value the other constraint rules out.
class DistConflictScalar;
  rand bit [3:0] x;
  constraint d {
    x dist {
      0 :/ 90,
      5 :/ 10
    };
  }
  constraint c {x != 0;}
endclass
// Heavy bucket is a range the other constraint rules out.
class DistConflictRange;
  rand bit [3:0] x;
  constraint d {
    x dist {
      [0 : 3] :/ 90,
      [12 : 15] :/ 10
    };
  }
  constraint c {x > 10;}
endclass
// Same, with the dist nested inside an if/else constraint.
class DistConflictIf;
  rand bit [3:0] x;
  rand bit sel;
  constraint s {sel == 1;}
  constraint d {
    if (sel) {
      x dist {
        [0 : 3] :/ 90,
        [12 : 15] :/ 10
      };
    } else {
      x dist {7 :/ 1};
    }
  }
  constraint c {x > 10;}
endclass
// Only the then arm holds a dist; the else arm holds a hard constraint.
class DistMixedArm;
  rand bit [3:0] x;
  rand bit sel;
  constraint s {sel == 1;}
  constraint d {
    if (sel) {
      x dist {
        [0 : 3] :/ 90,
        [12 : 15] :/ 10
      };
    } else {
      x == 7;
    }
  }
  constraint c {x > 10;}
endclass
// A dist in a one-armed constraint if is still only a preference.
class DistElseless;
  rand bit [3:0] x;
  rand bit sel;
  constraint s {sel == 1;}
  constraint d {
    if (sel)
    x dist {
      [0 : 3] :/ 90,
      [12 : 15] :/ 10
    };
  }
  constraint c {x > 10;}
endclass
// A hard and a soft constraint sharing an arm keep their own priorities, so
// the hard one holds and x is 2 every time.
class HardStaysHard;
  rand bit [3:0] x;
  rand bit sel;
  constraint s {sel == 1;}
  constraint d {
    if (sel) {
      x == 2;
      soft x == 1;
    }
  }
endclass
// Control: with nothing to conflict with, the weights still apply.
class DistNoConflict;
  rand bit [3:0] x;
  constraint d {
    x dist {
      [0 : 3] :/ 90,
      [12 : 15] :/ 10
    };
  }
endclass
// The membership constraint is hard, so this one has no solution at all.
class DistImpossible;
  rand bit [3:0] x;
  constraint d {
    x dist {
      0 :/ 90,
      5 :/ 10
    };
  }
  constraint c {x > 10;}
endclass
// The then arm holds only a dropped 'unique', so the collapse sees an else arm
// alone.  sel is solved to 1, so the else arm's constraint must not apply and x
// stays free.  Assigning sel a differing value beforehand catches a condition
// folded from that stale value rather than given to the solver.
// A dist shares an arm with a 'unique' on a dynamically sized array, which is
// unsupported inside a conditional constraint and is dropped.  The arm still
// holds both a hard and a soft constraint, so the weights must survive.
class DistBesideUnique;
  rand bit [3:0] v;
  rand bit [3:0] q[$];
  rand bit sel;
  constraint sz {q.size() == 3;}
  constraint s {sel == 1;}
  /* verilator lint_off CONSTRAINTIGN */
  constraint c {
    if (sel) {
      v dist {
        [0 : 3] :/ 90,
        [12 : 15] :/ 10
      };
      unique {q};
    } else {
      v == 7;
    }
  }
  /* verilator lint_on CONSTRAINTIGN */
endclass

class UniqueThenArm;
  rand bit [3:0] q[$];
  rand bit [3:0] x;
  rand bit sel;
  constraint sz {q.size() == 3;}
  constraint s {sel == 1;}
  // A 'unique' on a dynamically sized array inside a conditional constraint is
  // not supported and is dropped with a CONSTRAINTIGN warning, which leaves the
  // if with only its else arm.
  /* verilator lint_off CONSTRAINTIGN */
  constraint c {
    if (sel) {
      unique {q};
    } else {
      x == 3;
    }
  }
  /* verilator lint_on CONSTRAINTIGN */
endclass

module t;
  int nfail = 0;
  int hist[4];
  int ndistinct;
  bit [15:0] seen;
  int cnt, nok, ok;
  bit [1:0] sv, sv2;
  int svi;

  // Report one case.  `cnt` is the number of draws that landed in the
  // bucket of interest; [lo:hi] is the accepted band for it.
  task automatic report(string nm, int got, int lo, int hi, int okcnt, int draws);
    if (okcnt != draws) begin
      $write("%%Error: %-34s randomize() failed %0d/%0d\n", nm, draws - okcnt, draws);
      nfail++;
    end
    if (got < lo || got > hi) begin
      $write("%%Error: %-34s got=%0d exp=%0d..%0d\n", nm, got, lo, hi);
      nfail++;
    end
    else begin
      $write("   ok   %-34s got=%0d exp=%0d..%0d\n", nm, got, lo, hi);
    end
  endtask

  initial begin
    automatic Holder h = new;
    automatic Holder3 h3 = new;
    automatic HolderInt hi = new;
    automatic HolderWide hw = new;
    automatic MemberWeight mw = new;
    automatic QHolder qh = new;
    automatic ArrHolder ah = new;
    automatic Outer o = new;
    automatic TwoVar tv = new;
    automatic SideConstraint sc = new;
    automatic NarrowConstraint nc = new;
    automatic NegIdxArr na = new;
    automatic OpHolder oh = new;
    automatic ModeHolder mh = new;
    automatic Seq sq = new;
    automatic DistDerived dd = new;
    automatic DistBase db;
    automatic HistClassScope hcs = new;
    automatic DistConflictScalar cs = new;
    automatic DistConflictRange cr = new;
    automatic DistConflictIf ci = new;
    automatic DistMixedArm ma = new;
    automatic DistElseless el = new;
    automatic HardStaysHard hh = new;
    automatic DistNoConflict nc2 = new;
    automatic DistImpossible im = new;
    automatic UniqueThenArm ut = new;
    automatic DistBesideUnique bu = new;
    automatic int loc_wa, loc_wb;
    automatic bit [2:0] loc_lo, loc_hi;

    // verilog_format: off
    //==========================================================
    // A. Weight operator forms
    //==========================================================

    // A1  ':/' on scalar items.  0 gets 90/100.
    `chk("A1 :/ scalar", h.randomize() with { v dist { 0 :/ 90, 1 :/ 10 }; }, h.v == 0, 150, 200)

    // A2  ':=' on scalar items.  Identical meaning for single values.
    `chk("A2 := scalar", h.randomize() with { v dist { 0 := 9, 1 := 1 }; }, h.v == 0, 150, 200)

    // A3  An omitted weight means ':= 1', so each item is equally likely.
    //     Equal weights are still applied rather than left to the solver,
    //     which returns a satisfying assignment and not a uniform one.
    `chk("A3 omitted weight (uniform)", h.randomize() with { v dist { 0, 1 }; }, h.v == 0, 70, 130)

    // A4  Mixed ':=' and ':/' in one dist.  0 gets 27, [1:3] shares 3.
    `chk("A4 mixed := and :/", h.randomize() with { v dist { 0 := 27, [1 : 3] :/ 3 }; }, h.v == 0, 150, 200)

    // A5a ':=' on a range gives that weight to EACH value in the range.
    //     0 := 90 against [1:4] := 10 -> total 90+4*10 = 130, 0 is 69%.
    `chk("A5a := on range (per value)", h3.randomize() with { v dist { 0 := 90, [1 : 4] := 10 }; }, h3.v == 0, 110, 175)

    // A5b ':/' on a range divides the weight across the range.
    //     0 :/ 90 against [1:4] :/ 10 -> total 100, 0 is 90%.
    //     A5a and A5b together prove ':=' and ':/' are distinguished: an
    //     implementation that confused them would land outside one band.
    `chk("A5b :/ on range (divided)", h3.randomize() with { v dist { 0 :/ 90, [1 : 4] :/ 10 }; }, h3.v == 0, 150, 200)

    // A6  A zero weight removes the item from the set entirely.
    `chk("A6 zero weight excluded", h.randomize() with { v dist { 0 :/ 0, 1 :/ 5, 2 :/ 5 }; }, h.v == 0 || h.v == 3, 0, 0)

    // A7  All weights zero: the dist is vacuous, randomize still succeeds.
    cnt = 0;
    nok = 0;
    for (int i = 0; i < `N; i++) begin
      ok = h.randomize() with {
        v dist {
          0 :/ 0,
          1 :/ 0
        };
      };
      if (ok != 0) begin
        nok++;
        cnt++;
      end
    end
    report("A7 all-zero weights succeed", cnt, `N, `N, nok, `N);

    // A8  A single item is a hard equality: the value is fully determined.
    `chk("A8 single item", h.randomize() with { v dist { 1 :/ 5 }; }, h.v == 1, `N, `N)

    //==========================================================
    // B. Weight expression forms
    //==========================================================

    // B1  Weights read from class members.
    mw.wa = 90;
    mw.wb = 10;
    `chk("B1 weight from class member", mw.randomize() with { v dist { 0 :/ wa, 1 :/ wb }; }, mw.v == 0, 150, 200)

    // B2  Weights read from a local captured into the with-clause.  This form
    //     has no class-scope equivalent, it only exists inline.
    loc_wa = 90;
    loc_wb = 10;
    `chk("B2 weight from captured local", h.randomize() with { v dist { 0 :/ loc_wa, 1 :/ loc_wb }; }, h.v == 0, 150, 200)

    // B3  Weight as an arithmetic expression.
    loc_wa = 10;
    `chk("B3 weight expression", h.randomize() with { v dist { 0 :/ loc_wa * 9, 1 :/ loc_wa }; }, h.v == 0, 150, 200)

    //==========================================================
    // C. Item and bound forms
    //==========================================================

    // C1  Constant range items.
    `chk("C1 constant range", h3.randomize() with { v dist { [0 : 3] :/ 90, [4 : 7] :/ 10 }; }, h3.v <= 3, 150, 200)

    // C2  Range bounds taken from captured locals.
    loc_lo = 0;
    loc_hi = 3;
    `chk("C2 captured range bounds", h3.randomize() with { v dist { [loc_lo : loc_hi] :/ 90, [4 : 7] :/ 10 }; }, h3.v <= 3, 150, 200)

    // C3  Signed negative range on a rand int.
    `chk("C3 signed negative range", hi.randomize() with { x dist { [-9 : -5] :/ 90, [-4 : 0] :/ 10 }; }, hi.x <= -5, 150, 200)

    // C4  Signed negative scalar items, spelled as literal expressions rather
    //     than as the equivalent single-value ranges C3 uses.
    `chk("C4 negative scalars", hi.randomize() with { x dist { -5 :/ 90, 5 :/ 10 }; }, hi.x == -5, 150, 200)

    // C5  Wide (>32 bit) values.
    `chk("C5 wide values", hw.randomize() with { x dist { 40'd0 :/ 90, 40'hff_ffff_ffff :/ 10 }; }, hw.x == 40'd0, 150, 200)

    // C6  Whole-container item 'dist {que}'.  Weights are all 1 here, so this
    //     checks membership only: every draw must be one of the queue values.
    qh.que = '{3, 5, 7};
    `chk("C6 whole-container membership", qh.randomize() with { v dist { que }; }, qh.v != 3 && qh.v != 5 && qh.v != 7, 0, 0)

    //==========================================================
    // D. Inline call forms
    //==========================================================

    // D1  randomize(args) with {} -- the form a UVM sequence writes.
    `chk("D1 randomize(v) with {}", h.randomize( v ) with { v dist { 0 :/ 90, 1 :/ 10 }; }, h.v == 0, 150, 200)

    // D2  std::randomize(v) with {} -- what DV_CHECK_STD_RANDOMIZE_WITH_FATAL
    //     expands to.
    `chk("D2 std::randomize(v) with {}", std::randomize( sv ) with { sv dist { 0 :/ 90, 1 :/ 10 }; }, sv == 0, 150, 200)

    // D3  std::randomize over two variables, dist on one of them.
    `chk("D3 std::randomize two vars", std::randomize( sv, sv2 ) with { sv dist { 0 :/ 90, 1 :/ 10 }; sv2 < 2; }, sv == 0, 150, 200)

    // D4  std::randomize with a dist on each of two variables.
    `chk("D4 std::randomize two dists", std::randomize( sv, sv2 ) with { sv dist { 0 :/ 90, 1 :/ 10 }; sv2 dist { 2 :/ 90, 3 :/ 10 }; }, sv == 0 && sv2 == 2, 130, 200)

    // D5  std::randomize on a signed int, with negative scalar items.
    `chk("D5 std::randomize signed", std::randomize( svi ) with { svi dist { -5 :/ 90, 5 :/ 10 }; }, svi == -5, 150, 200)

    // D6  The restricted 'with (ids) {}' form (IEEE 1800-2023 18.7), which
    //     names the variables the clause is allowed to constrain.
    `chk("D6 with (ids) {} form", h.randomize() with ( v) { v dist { 0 :/ 90, 1 :/ 10 }; }, h.v == 0, 150, 200)

    //==========================================================
    // E. Structural contexts inside the with-clause
    //==========================================================

    // E1  dist inside an if/else constraint.
    `chk("E1 dist inside if/else", tv.randomize() with { w == 1; if (w == 1) { v dist { 0 :/ 90, 1 :/ 10 }; } else { v dist { 2 :/ 90, 3 :/ 10 }; } }, tv.v == 0, 150, 200)

    // E2  dist inside a foreach constraint.  4 elements per draw.
    cnt = 0;
    nok = 0;
    for (int i = 0; i < `N; i++) begin
      ok = ah.randomize() with {
        foreach (a[j])
        a[j] dist {
          [0 : 1] :/ 90,
          [2 : 7] :/ 10
        };
      };
      if (ok != 0) begin
        nok++;
        for (int j = 0; j < 4; j++) if (ah.a[j] <= 1) cnt++;
      end
    end
    report("E2 dist inside foreach", cnt, 620, 800, nok, `N);

    // E3  dist as the consequent of an implication.
    `chk("E3 dist under implication", tv.randomize() with { w == 1; (w == 1) -> v dist { 0 :/ 90, 1 :/ 10 }; }, tv.v == 0, 150, 200)

    // E4  soft dist.
    `chk("E4 soft dist", h.randomize() with { soft v dist { 0 :/ 90, 1 :/ 10 }; }, h.v == 0, 150, 200)

    // E5  dist on a member-select through a rand sub-object.
    `chk("E5 dist on member-select", o.randomize() with { inn.v dist { 0 :/ 90, 1 :/ 10 }; }, o.inn.v == 0, 150, 200)

    // E6  dist on one element of a rand array.
    `chk("E6 dist on array element", ah.randomize() with { a[1] dist { [0 : 1] :/ 90, [2 : 7] :/ 10 }; }, ah.a[1] <= 1, 150, 200)

    // E7  dist alongside a constraint on a different variable.
    `chk("E7 dist plus sibling constraint", tv.randomize() with { v dist { 0 :/ 90, 1 :/ 10 }; w == 3; }, tv.v == 0 && tv.w == 3, 150, 200)

    // E8  dist alongside a *compatible* constraint on the same variable.
    //     The extra constraint does not exclude either dist bucket.
    `chk("E8 dist plus compatible bound", h.randomize() with { v dist { 0 :/ 90, 1 :/ 10 }; v <= 1; }, h.v == 0, 150, 200)

    // E9  dist alongside a constraint that excludes the heaviest bucket.  The
    //     set and the constraint still intersect, at [12:15], so randomize()
    //     succeeds every time and lands there.
    `chk("E9 dist plus excluding bound", qh.randomize() with { v dist { [0 : 3] :/ 90, [12 : 15] :/ 10 }; v > 10; }, qh.v >= 12, `N, `N)

    //==========================================================
    // F. Interaction with class-scope constraints
    //==========================================================

    // F1  Class constrains another variable; inline dist must still weight.
    `chk("F1 class constr, other var", sc.randomize() with { v dist { 0 :/ 90, 1 :/ 10 }; }, sc.v == 0 && sc.w > 9, 150, 200)

    // F2  Class constrains the same variable, compatibly with the dist.
    `chk("F2 class constr, same var", nc.randomize() with { v dist { 0 :/ 90, 1 :/ 10 }; }, nc.v == 0, 150, 200)

    // F3  Two successive inline dists on the same object must not leak state
    //     into one another.
    cnt = 0;
    nok = 0;
    for (int i = 0; i < `N; i++) begin
      ok = h.randomize() with {
        v dist {
          0 :/ 90,
          1 :/ 10
        };
      };
      if (ok != 0) begin
        ok = h.randomize() with {
          v dist {
            3 :/ 90,
            2 :/ 10
          };
        };
        if (ok != 0) begin
          nok++;
          if (h.v == 3) cnt++;
        end
      end
    end
    report("F3 successive inline dists", cnt, 165, 200, nok, `N);

    //==========================================================
    // G. Data shapes a testbench commonly writes
    //==========================================================

    // G1  An enum-typed rand variable, weighted by enumeration name.
    `chk("G1 enum-typed items", oh.randomize() with { op dist { OP_RD :/ 90, OP_WR :/ 10 }; }, oh.op == OP_RD, 150, 200)

    // G2  foreach over an unpacked array whose bounds are neither zero-based
    //     nor ascending.  8 elements per draw, 90% of them in [0:1].
    cnt = 0;
    nok = 0;
    for (int i = 0; i < `N; i++) begin
      ok = na.randomize() with {
        foreach (a[j])
        a[j] dist {
          [0 : 1] :/ 90,
          [2 : 7] :/ 10
        };
      };
      if (ok != 0) begin
        nok++;
        for (int j = -2; j <= 5; j++) if (na.a[j] <= 1) cnt++;
      end
    end
    report("G2 descending array bounds", cnt, 1240, 1600, nok, `N);

    // G3  A variable frozen with rand_mode(0) holds its value, and an inline
    //     dist naming it is satisfied by that value while it is in the set.
    mh.v = 0;
    mh.v.rand_mode(0);
    `chk("G3 rand_mode(0) frozen in set", mh.randomize() with { v dist { 0 :/ 90, 3 :/ 10 }; }, mh.v == 0, `N, `N)
    mh.v.rand_mode(1);

    //==========================================================
    // H. Call and inheritance contexts
    //==========================================================

    // H1  The clause is written inside a class method and takes its weight
    //     from a member of the same object.
    `chk("H1 in a method, member weight", sq.go_member(), sq.v == 0, 150, 200)

    // H2  The same, with the weight in a variable local to the method.
    `chk("H2 in a method, local weight", sq.go_local(), sq.v == 0, 150, 200)

    // H3  A member declared in a base class, randomized through a handle of
    //     the derived type.
    `chk("H3 base member, derived handle", dd.randomize() with { v dist { 0 :/ 90, 1 :/ 10 }; }, dd.v == 0, 150, 200)

    // H4  The same object through a handle of the base type.
    db = dd;
    `chk("H4 base member, base handle", db.randomize() with { v dist { 0 :/ 90, 1 :/ 10 }; }, db.v == 0, 150, 200)

    //==========================================================
    // I. Every bucket of one distribution, inline and at class scope
    //==========================================================

    // I1  All four buckets of an inline dist, not just the heaviest, so a
    //     weight applied to the wrong item is caught as well as one dropped.
    foreach (hist[i]) hist[i] = 0;
    nok = 0;
    for (int i = 0; i < `N; i++) begin
      ok = h.randomize() with {
        v dist {
          0 :/ 70,
          1 :/ 10,
          2 :/ 10,
          3 :/ 10
        };
      };
      if (ok != 0) begin
        nok++;
        hist[h.v]++;
      end
    end
    report("I1 inline histogram bucket 0", hist[0], 110, 170, nok, `N);
    report("I1 inline histogram bucket 1", hist[1], 6, 38, nok, `N);
    report("I1 inline histogram bucket 2", hist[2], 6, 38, nok, `N);
    report("I1 inline histogram bucket 3", hist[3], 6, 38, nok, `N);

    // I2  Control: the same distribution written at class scope.
    foreach (hist[i]) hist[i] = 0;
    nok = 0;
    for (int i = 0; i < `N; i++) begin
      ok = hcs.randomize();
      if (ok != 0) begin
        nok++;
        hist[hcs.v]++;
      end
    end
    report("I2 class-scope bucket 0", hist[0], 110, 170, nok, `N);
    report("I2 class-scope bucket 1", hist[1], 6, 38, nok, `N);
    report("I2 class-scope bucket 2", hist[2], 6, 38, nok, `N);
    report("I2 class-scope bucket 3", hist[3], 6, 38, nok, `N);

    //==========================================================
    // J. The bucket choice is a preference, not a requirement
    //==========================================================

    // J1  A hard constraint excluding the heavy bucket leaves the other one,
    //     so randomize() succeeds and uses it.
    `chk("J1 scalar bucket excluded", cs.randomize(), cs.x == 5, `N, `N)

    // J2  The same with the heavy bucket a range.
    `chk("J2 range bucket excluded", cr.randomize(), cr.x >= 12, `N, `N)

    // J3  The dist nested in a constraint if.
    `chk("J3 dist in a constraint if", ci.randomize(), ci.x >= 12, `N, `N)

    // J4  One arm holds the dist, the other only a hard constraint.
    `chk("J4 dist in one arm only", ma.randomize(), ma.x >= 12, `N, `N)

    // J5  An if with no else arm.
    `chk("J5 one-armed constraint if", el.randomize(), el.x >= 12, `N, `N)

    // J6  A hard constraint sharing an arm with a soft one keeps priority.
    `chk("J6 hard beside soft in an arm", hh.randomize(), hh.x == 2, `N, `N)

    // J7  Unopposed, the weights still apply.
    `chk("J7 unopposed weights", nc2.randomize(), nc2.x <= 3, 140, 200)

    // J8  An empty intersection of the set and the constraint has no solution.
    cnt = 0;
    nok = 0;
    for (int i = 0; i < `N; i++) begin
      ok = im.randomize();
      nok++;
      if (ok == 0) cnt++;
    end
    report("J8 empty intersection fails", cnt, `N, `N, nok, `N);

    // J10 A dist sharing an arm with a dropped 'unique' keeps its weights.
    `chk("J10 dist beside a dropped unique", bu.randomize(), bu.v <= 3, 150, 200)

    // J9  A 'unique' empties the other arm, leaving an else-only collapse.
    //     x is unconstrained, so it must range rather than take the else
    //     arm's value.
    seen = 0;
    nok = 0;
    for (int i = 0; i < `N; i++) begin
      ut.sel = 0;
      ok = ut.randomize();
      if (ok != 0) begin
        nok++;
        seen[ut.x] = 1'b1;
      end
    end
    ndistinct = 0;
    for (int v = 0; v < 16; v++) if (seen[v]) ndistinct++;
    report("J9 else-only collapse", ndistinct, 8, 16, nok, `N);


    //==========================================================

    // verilog_format: on

    if (nfail != 0) begin
      $write("%%Error: %0d check(s) failed\n", nfail);
      `stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
