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

// Two-value domain, one feasible: the failing draw is consumed
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

// Two cycling variables keep the joint solve, so this class still shows the
// unfixed behaviour: no call ever fails
class TwoRandc;
  randc bit a;
  randc bit b;
  rand bit x;
  constraint pin_x {x == 1;}
  constraint rel {x == (a ^ b);}
endclass

// A randc member with no constraint never reaches the solver, so the draw still
// applies to the one that does
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
  TwoRandc two;
  OneCycling one;
  ModeOff mo;
  int ok;
  int good;
  int fails;
  bit [3:0] seen;
  bit [15:0] seenHex;
  int count[4];
  bit [1:0] prevc;
  bit [1:0] prevx;

  initial begin
    // Flat: successes satisfy the relation, c == 3 never succeeds, and a
    // failed call leaves both variables at their previous values
    f = new;
    f.srandom(11);
    good = 0;
    fails = 0;
    seen = 4'b0;
    for (int i = 0; i < 12; ++i) begin
      prevc = f.c;
      prevx = f.x;
      ok = f.randomize();
      if (ok == 0) begin
        ++fails;
        `checkd(f.c, prevc);
        `checkd(f.x, prevx);
      end
      else begin
        ++good;
        `checkd(f.c < f.x, 1'b1);
        seen[f.c] = 1'b1;
        ++count[f.c];
        if (good % 3 == 0) begin
          `checkd(seen, 4'b0111);
          seen = 4'b0;
        end
      end
    end
    `checkd(good + fails, 12);
    `checkd(count[3], 0);  // zero-ok: c == 3 satisfies no x
    `checkd(good, 10);
    `checkd(fails, 2);

    // OneBit: only c == 0 admits x
    ob = new;
    ob.srandom(22);
    good = 0;
    fails = 0;
    for (int i = 0; i < 10; ++i) begin
      ok = ob.randomize();
      if (ok == 0)++fails;
      else begin
        ++good;
        `checkd(ob.c, 0);  // zero-ok: sole feasible randc value
        `checkd(ob.x, 1);
      end
    end
    `checkd(good + fails, 10);
    `checkd(good, 7);
    `checkd(fails, 3);

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

    // Enumc: members only; BLUE/WHITE/BLACK admit no limit
    en = new;
    en.srandom(44);
    good = 0;
    fails = 0;
    for (int i = 0; i < 15; ++i) begin
      ok = en.randomize();
      if (ok == 0)++fails;
      else begin
        ++good;
        `checkd(en.color < en.limit, 1'b1);
      end
    end
    `checkd(good + fails, 15);
    `checkd(good, 7);
    `checkd(fails, 8);

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

    // Phased: the same failure semantics through solve...before layers
    ph = new;
    ph.srandom(60);
    good = 0;
    fails = 0;
    for (int i = 0; i < 12; ++i) begin
      ok = ph.randomize();
      if (ok == 0)++fails;
      else begin
        ++good;
        `checkd(ph.c < ph.x, 1'b1);
        `checkd(ph.y > {2'b00, ph.x}, 1'b1);
      end
    end
    `checkd(good + fails, 12);
    `checkd(good, 10);
    `checkd(fails, 2);

    // Top: dotted-path randc drawn first, same rule through a global constraint
    tp = new;
    tp.srandom(77);
    good = 0;
    fails = 0;
    for (int i = 0; i < 12; ++i) begin
      ok = tp.randomize();
      if (ok == 0)++fails;
      else begin
        ++good;
        `checkd(tp.s.c < tp.x, 1'b1);
      end
    end
    `checkd(good + fails, 12);
    `checkd(good, 9);
    `checkd(fails, 3);

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

    // TwoRandc: the joint solve keeps every call succeeding, as before the fix
    two = new;
    two.srandom(155);
    good = 0;
    fails = 0;
    for (int i = 0; i < 12; ++i) begin
      ok = two.randomize();
      if (ok == 0)++fails;
      else begin
        ++good;
        `checkd(two.a ^ two.b, 1'b1);
      end
    end
    `checkd(good, 12);
    `checkd(fails, 0);  // zero-ok: the joint solve never picks an infeasible pair

    // OneCycling: an unconstrained randc member is not one the solver cycles,
    // so c is still drawn ahead of x
    one = new;
    one.srandom(11);
    good = 0;
    fails = 0;
    for (int i = 0; i < 12; ++i) begin
      ok = one.randomize();
      if (ok == 0)++fails;
      else begin
        ++good;
        `checkd(one.c < one.x, 1'b1);
      end
    end
    `checkd(good, 10);
    `checkd(fails, 2);

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

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
