// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// randc solved before rand: an infeasible randc draw fails the call
class Flat;
  randc bit [1:0] c;
  rand bit [1:0] x;
  constraint rel_c {c < x;}
endclass

// Two-value domain, one feasible
class OneBit;
  randc bit c;
  rand bit x;
  constraint rel_c {c < x;}
endclass

// Constraint on the randc variable alone filters the domain, never fails
class RandcOnly;
  randc bit [1:0] c;
  constraint no3 {c != 3;}
endclass

// Enum randc: the permutation covers members only; rand-coupled failures apply
class Enumc;
  typedef enum bit [2:0] {
    RED = 0,
    GREEN = 1,
    BLUE = 2,
    WHITE = 3,
    BLACK = 4
  } color_t;
  randc color_t color;
  rand bit [2:0] limit;
  constraint c_lim {limit <= 2;}
  constraint c_rel {color < limit;}
endclass

// No randc value admits a solution: genuine unsat, not a cyclic miss
class AllUnsat;
  randc bit [1:0] c;
  rand bit [1:0] x;
  constraint pin_x {x == 0;}
  constraint rel_c {c < x;}
endclass

// randc precedes solve...before layers; failures surface in the phased path
class Phased;
  randc bit [1:0] c;
  rand bit [1:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint rel_c {y > {2'b00, x};}
  constraint link_c {c < x;}
endclass

// Global constraint reaching a sub-object randc through a dotted path
class Sub;
  randc bit [1:0] c;
endclass

class Top;
  rand bit [1:0] x;
  rand Sub s;
  constraint g {s.c < x;}
  function new;
    s = new;
  endfunction
endclass

// Four-bit randc: the cycle covers the whole constrained domain
class RandcHex;
  randc bit [3:0] c;
  constraint lim {c < 12;}
endclass

// The randc-only constraint itself is unsatisfiable: a reported unsat, not a cycle miss
class RandcUnsat;
  randc bit [1:0] c;
  constraint imp {c > 3;}
endclass

// The draw runs ahead of the layers, so a dead randc domain fails there
class PhasedUnsat;
  randc bit [1:0] c;
  rand bit [1:0] x;
  rand bit [3:0] y;
  constraint order {solve x before y;}
  constraint imp {c > 3;}
  constraint dep {y > {2'b00, x};}
endclass

// Layered solve where no randc value works: fails on a fresh cycle too
class PhasedAllUnsat;
  randc bit [1:0] c;
  rand bit [1:0] x;
  rand bit [3:0] y;
  constraint order {solve x before y;}
  constraint pin_x {x == 0;}
  constraint rel {c < x;}
  constraint dep {y > {2'b00, x};}
endclass

// A randc member with no constraint leaves the constrained one cycling as before
class OneCycling;
  randc bit [1:0] c;
  randc bit [1:0] d;
  rand bit [1:0] x;
  constraint rel {c < x;}
endclass

// rand_mode off leaves the randc variable fixed and out of the draw
class ModeOff;
  randc bit [1:0] c;
  rand bit [1:0] x;
  constraint rel {c < x;}
endclass

// rand_mode off on the rand side turns the relation into a filter on the randc domain
class ModeOffRand;
  randc bit [1:0] c;
  rand bit [1:0] x;
  constraint rel {c < x;}
endclass

// A state variable in the relation only bounds the randc domain
class StateBound;
  randc bit [1:0] c;
  bit [1:0] lim;
  constraint rel {c < lim;}
  constraint guard {lim != 0;}
endclass

// A class handle array element in the relation: the same cycles through a dynamic path
class Item;
  rand bit [1:0] v;
endclass

class ArrayRel;
  randc bit [1:0] c;
  rand Item items[2];
  constraint rel {c < items[0].v;}
  function new;
    foreach (items[i]) items[i] = new;
  endfunction
endclass

module t;
  Flat f;
  OneBit ob;
  RandcOnly ro;
  Enumc en;
  AllUnsat au;
  Phased ph;
  Top tp;
  RandcHex rh;
  RandcUnsat ru;
  PhasedUnsat pu;
  PhasedAllUnsat pa;
  OneCycling one;
  ModeOff mo;
  ModeOffRand mr;
  StateBound sb;
  ArrayRel ar;
  int ok;
  int good;
  int fails;
  bit [3:0] seen;
  bit [15:0] seenHex;
  int fcount[4];
  int ecount[5];
  int pcount[4];
  int tcount[4];
  int ocount[4];
  int acount[4];
  bit [1:0] prevc;
  bit [1:0] prevx;

  initial begin
    // Flat: three cycles of the three feasible values; c == 3 never succeeds
    // and a failed call leaves both variables at their previous values
    f = new;
    f.srandom(11);
    good = 0;
    seen = 4'b0;
    for (int i = 0; i < 16 && good < 9; ++i) begin
      prevc = f.c;
      prevx = f.x;
      ok = f.randomize();
      if (ok == 0) begin
        `checkd(f.c, prevc);
        `checkd(f.x, prevx);
      end
      else begin
        ++good;
        `checkd(f.c < f.x, 1'b1);
        seen[f.c] = 1'b1;
        ++fcount[f.c];
        if (good % 3 == 0) begin
          `checkd(seen, 4'b0111);
          seen = 4'b0;
        end
      end
    end
    `checkd(good, 9);
    for (int v = 0; v < 3; ++v) `checkd(fcount[v], 3);
    `checkd(fcount[3], 0);  // zero-ok: c == 3 satisfies no x

    // OneBit: only c == 0 admits x
    ob = new;
    ob.srandom(22);
    good = 0;
    for (int i = 0; i < 12 && good < 4; ++i) begin
      ok = ob.randomize();
      if (ok == 1) begin
        ++good;
        `checkd(ob.c, 0);  // zero-ok: sole feasible randc value
        `checkd(ob.x, 1);
      end
    end
    `checkd(good, 4);

    // RandcOnly: filtered three-value cycles, every call succeeds
    ro = new;
    ro.srandom(33);
    seen = 4'b0;
    for (int i = 0; i < 6; ++i) begin
      ok = ro.randomize();
      `checkd(ok, 1);
      if (i % 3 == 2) begin
        `checkd(seen | (4'b1 << ro.c), 4'b0111);
        seen = 4'b0;
      end
      else begin
        seen[ro.c] = 1'b1;
      end
    end

    // Enumc: members only; BLUE, WHITE and BLACK admit no limit
    en = new;
    en.srandom(44);
    good = 0;
    for (int i = 0; i < 24 && good < 6; ++i) begin
      ok = en.randomize();
      if (ok == 1) begin
        ++good;
        `checkd(en.color < en.limit, 1'b1);
        ++ecount[int'(en.color)];
      end
    end
    `checkd(good, 6);
    `checkd(ecount[0], 3);
    `checkd(ecount[1], 3);
    for (int v = 2; v < 5; ++v) `checkd(ecount[v], 0);  // zero-ok: no limit above them

    // AllUnsat: every call fails and reports; values are retained
    au = new;
    au.srandom(55);
    au.c = 2;
    au.x = 1;
    fails = 0;
    for (int i = 0; i < 4; ++i) begin
      ok = au.randomize();
      if (ok == 0)++fails;
    end
    `checkd(fails, 4);
    `checkd(au.c, 2);
    `checkd(au.x, 1);

    // Phased: the same cycles through solve...before layers
    ph = new;
    ph.srandom(60);
    good = 0;
    for (int i = 0; i < 16 && good < 9; ++i) begin
      ok = ph.randomize();
      if (ok == 1) begin
        ++good;
        `checkd(ph.c < ph.x, 1'b1);
        `checkd(ph.y > {2'b00, ph.x}, 1'b1);
        ++pcount[ph.c];
      end
    end
    `checkd(good, 9);
    for (int v = 0; v < 3; ++v) `checkd(pcount[v], 3);
    `checkd(pcount[3], 0);  // zero-ok: c == 3 satisfies no x

    // Top: dotted-path randc, the same cycles through a global constraint
    tp = new;
    tp.srandom(77);
    good = 0;
    for (int i = 0; i < 16 && good < 9; ++i) begin
      ok = tp.randomize();
      if (ok == 1) begin
        ++good;
        `checkd(tp.s.c < tp.x, 1'b1);
        ++tcount[tp.s.c];
      end
    end
    `checkd(good, 9);
    for (int v = 0; v < 3; ++v) `checkd(tcount[v], 3);
    `checkd(tcount[3], 0);  // zero-ok: s.c == 3 satisfies no x

    // RandcHex: 12-value domain, one full cycle, every call succeeds
    rh = new;
    rh.srandom(88);
    good = 0;
    fails = 0;
    seenHex = 16'b0;
    for (int i = 0; i < 12; ++i) begin
      ok = rh.randomize();
      if (ok == 0)++fails;
      else begin
        ++good;
        `checkd(rh.c < 12, 1'b1);
        seenHex[rh.c] = 1'b1;
      end
    end
    `checkd(good, 12);
    `checkd(fails, 0);  // zero-ok: a randc-only constraint filters, never fails
    `checkd(seenHex, 16'h0fff);

    // RandcUnsat: no randc value at all, so every call reports and retains
    ru = new;
    ru.srandom(99);
    ru.c = 2;
    fails = 0;
    for (int i = 0; i < 3; ++i) begin
      ok = ru.randomize();
      if (ok == 0)++fails;
    end
    `checkd(fails, 3);
    `checkd(ru.c, 2);

    // PhasedUnsat: the dead domain surfaces in the draw, ahead of the layers
    pu = new;
    pu.srandom(111);
    pu.c = 2;
    fails = 0;
    for (int i = 0; i < 3; ++i) begin
      ok = pu.randomize();
      if (ok == 0)++fails;
    end
    `checkd(fails, 3);
    `checkd(pu.c, 2);

    // PhasedAllUnsat: drawn value fails and no other value would do better
    pa = new;
    pa.srandom(122);
    pa.c = 3;
    fails = 0;
    for (int i = 0; i < 3; ++i) begin
      ok = pa.randomize();
      if (ok == 0)++fails;
    end
    `checkd(fails, 3);
    `checkd(pa.c, 3);

    // OneCycling: the unconstrained randc member does not disturb c's cycles
    one = new;
    one.srandom(11);
    good = 0;
    for (int i = 0; i < 16 && good < 9; ++i) begin
      ok = one.randomize();
      if (ok == 1) begin
        ++good;
        `checkd(one.c < one.x, 1'b1);
        ++ocount[one.c];
      end
    end
    `checkd(good, 9);
    for (int v = 0; v < 3; ++v) `checkd(ocount[v], 3);
    `checkd(ocount[3], 0);  // zero-ok: c == 3 satisfies no x

    // ModeOff: the randc variable stays fixed and still constrains x
    mo = new;
    mo.srandom(133);
    mo.c = 1;
    void'(mo.c.rand_mode(0));
    good = 0;
    fails = 0;
    for (int i = 0; i < 6; ++i) begin
      ok = mo.randomize();
      if (ok == 0)++fails;
      else begin
        ++good;
        `checkd(mo.c, 1);
        `checkd(mo.c < mo.x, 1'b1);
      end
    end
    `checkd(good, 6);
    `checkd(fails, 0);  // zero-ok: the drawn set is empty, nothing can fail cyclically

    // ModeOffRand: x fixed at 2 makes the relation a filter on c, so c cycles
    // through the two values below it and no call fails
    mr = new;
    mr.srandom(144);
    mr.x = 2;
    void'(mr.x.rand_mode(0));
    seen = 4'b0;
    for (int i = 0; i < 6; ++i) begin
      ok = mr.randomize();
      `checkd(ok, 1);
      `checkd(mr.x, 2);
      seen[mr.c] = 1'b1;
      if (i % 2 == 1) begin
        `checkd(seen, 4'b0011);
        seen = 4'b0;
      end
    end

    // StateBound: the same two-value cycles under a state variable bound
    sb = new;
    sb.srandom(166);
    sb.lim = 2;
    seen = 4'b0;
    for (int i = 0; i < 6; ++i) begin
      ok = sb.randomize();
      `checkd(ok, 1);
      seen[sb.c] = 1'b1;
      if (i % 2 == 1) begin
        `checkd(seen, 4'b0011);
        seen = 4'b0;
      end
    end

    // ArrayRel: the element's value bounds c the way x does in Flat
    ar = new;
    ar.srandom(177);
    good = 0;
    for (int i = 0; i < 16 && good < 9; ++i) begin
      ok = ar.randomize();
      if (ok == 1) begin
        ++good;
        `checkd(ar.c < ar.items[0].v, 1'b1);
        ++acount[ar.c];
      end
    end
    `checkd(good, 9);
    for (int v = 0; v < 3; ++v) `checkd(acount[v], 3);
    `checkd(acount[3], 0);  // zero-ok: c == 3 satisfies no element value

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
