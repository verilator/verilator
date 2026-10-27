// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// randc values excluded by the value of another rand variable: c cannot be 3
class Phased;
  randc bit [1:0] c;
  rand bit [1:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint rel_c {y > {2'b00, x};}
  constraint link_c {c < x;}
endclass

// Three dependency layers, so exhaustion lands two phases before the last
class Layered;
  randc bit [1:0] c;
  rand bit [3:0] a;
  rand bit [3:0] b;
  rand bit [3:0] d;
  constraint order_ab {solve a before b;}
  constraint order_bd {solve b before d;}
  constraint rel_c {
    b > a;
    d > b;
  }
endclass

// Constraint on the randc variable alone, so the permutation itself holds three values
class Limited;
  randc bit [1:0] c;
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint rel_c {y > x;}
  constraint lim_c {c != 2'd3;}
endclass

// randc tied to a solve-before variable, so x cycles only if the exclusions reach phase one
class Ordered;
  randc bit [1:0] c;
  rand bit [1:0] x;
  rand bit [1:0] y;
  constraint order_c {solve x before y;}
  constraint tie_c {x == c;}
  constraint rel_c {y == ~x;}
endclass

// Unsatisfiable before any randc value is recorded
class Unsat;
  randc bit [1:0] c;
  rand bit [3:0] x;
  rand bit [3:0] y;
  constraint order_c {solve x before y;}
  constraint rel_c {y > x;}
endclass

// randc solved before rand (IEEE 1800-2023 18.4.2): an infeasible randc draw fails the call
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

// No randc value admits a solution: genuine unsat, not a cyclic miss
class AllUnsat;
  randc bit [1:0] c;
  rand bit [1:0] x;
  constraint pin_x {x == 0;}
  constraint rel_c {c < x;}
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

// An inline with clause is the only constraint on the randc variable
class InlineOnly;
  randc bit [1:0] c;
endclass

// Fault injection only (t_randomize_solver_randc): two randc variables keep the joint solve
class TwoRandc;
  randc bit a;
  randc bit b;
  rand bit x;
  constraint pin_x {x == 1;}
  constraint rel {x == (a ^ b);}
endclass

// Fault injection only: the randc variable is named b, which the malformed-value tampers target
class BadDraw;
  randc bit [1:0] b;
  rand bit [1:0] x;
  constraint rel {x == b;}
endclass

module t;
  Phased p;
  Layered q;
  Limited r;
  Ordered o;
  Unsat u;
  bit [3:0] seen;
  int pcount[4];
  int qcount[4];
  int rcount[4];
  int ocount[4];
  int ok;
  int psolved;


  // t_randomize_solver_randc runs one scenario per +MODE, alone, so the replies its
  // TAMPER_AT counts start at that scenario's first call. Seeds are fixed per scenario.
  task automatic fault_mode(string mode);
    automatic int good = 0;
    automatic int fails = 0;
    automatic int ok;
    if (mode == "phased") begin
      automatic Phased ph = new;
      ph.srandom(60);
      for (int i = 0; i < 12; ++i) begin
        ok = ph.randomize();
        if (ok == 0)++fails;
        else ++good;
      end
    end
    else if (mode == "two") begin
      automatic TwoRandc two = new;
      two.srandom(155);
      for (int i = 0; i < 12; ++i) begin
        ok = two.randomize();
        if (ok == 0)++fails;
        else ++good;
      end
    end
    else if (mode == "bad_draw") begin
      automatic BadDraw bad = new;
      bad.srandom(7);
      for (int i = 0; i < 6; ++i) begin
        ok = bad.randomize();
        if (ok == 0)++fails;
        else ++good;
      end
    end
    else begin
      automatic Flat f = new;
      f.srandom(11);
      for (int i = 0; i < 6; ++i) begin
        ok = f.randomize();
        if (ok == 0)++fails;
        else ++good;
      end
    end
    $write("NPASS=%0d NFAIL=%0d\n", good, fails);
  endtask

  initial begin : checks
    string mode;
    if ($value$plusargs("MODE=%s", mode)) begin
      fault_mode(mode);
      $write("*-* All Finished *-*\n");
      $finish;
      // $finish ends the run only after this process stops, so leave before the checks
      disable checks;
    end

    // c == 3 satisfies no x
    p = new;
    seen = 4'b0;
    psolved = 0;
    for (int i = 0; i < 12 && psolved < 9; ++i) begin
      if (p.randomize() == 1) begin
        `checkd(p.y > {2'b00, p.x}, 1'b1);
        `checkd(p.c < p.x, 1'b1);
        seen[p.c] = 1'b1;
        ++pcount[p.c];
        ++psolved;
        if (psolved % 3 == 0) begin
          `checkd(seen, 4'b0111);  // Three draws covered three values, so none repeated
          seen = 4'b0;
        end
      end
    end
    `checkd(psolved, 9);  // Three cycles of three solvable values
    for (int v = 0; v < 3; ++v) `checkd(pcount[v], 3);
    `checkd(pcount[3], 0);  // zero-ok: c == 3 satisfies no x

    q = new;
    seen = 4'b0;
    for (int i = 0; i < 8; ++i) begin
      ok = q.randomize();
      `checkd(ok, 1);
      `checkd(q.b > q.a, 1'b1);
      `checkd(q.d > q.b, 1'b1);
      seen[q.c] = 1'b1;
      ++qcount[q.c];
      if (i % 4 == 3) begin
        `checkd(seen, 4'b1111);
        seen = 4'b0;
      end
    end
    for (int v = 0; v < 4; ++v) `checkd(qcount[v], 2);

    r = new;
    seen = 4'b0;
    for (int i = 0; i < 6; ++i) begin
      ok = r.randomize();
      `checkd(ok, 1);
      `checkd(r.y > r.x, 1'b1);
      seen[r.c] = 1'b1;
      ++rcount[r.c];
      if (i % 3 == 2) begin
        `checkd(seen, 4'b0111);
        seen = 4'b0;
      end
    end
    for (int v = 0; v < 3; ++v) `checkd(rcount[v], 2);
    `checkd(rcount[3], 0);  // zero-ok: excluded by lim_c

    o = new;
    seen = 4'b0;
    for (int i = 0; i < 8; ++i) begin
      ok = o.randomize();
      `checkd(ok, 1);
      `checkd(o.x, o.c);
      `checkd(o.y, ~o.x);
      seen[o.x] = 1'b1;
      ++ocount[o.x];
      if (i % 4 == 3) begin
        `checkd(seen, 4'b1111);
        seen = 4'b0;
      end
    end
    for (int v = 0; v < 4; ++v) `checkd(ocount[v], 2);

    // Fails with an empty cycle, then the object still randomizes
    u = new;
    ok = u.randomize() with {
      x > 14;
      y > x;
    };
    `checkd(ok, 0);  // zero-ok: constraints are unsatisfiable
    ok = u.randomize();
    `checkd(ok, 1);
    `checkd(u.y > u.x, 1'b1);

    // Flat: three cycles of the three feasible values; c == 3 never succeeds
    // and a failed call leaves both variables at their previous values
    begin
      automatic Flat f = new;
      automatic int good = 0;
      automatic int fcount[4] = '{default: 0};
      automatic bit [1:0] prevc;
      automatic bit [1:0] prevx;
      f.srandom(11);
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
    end

    // OneBit: only c == 0 admits x
    begin
      automatic OneBit ob = new;
      automatic int good = 0;
      ob.srandom(22);
      for (int i = 0; i < 12 && good < 4; ++i) begin
        ok = ob.randomize();
        if (ok == 1) begin
          ++good;
          `checkd(ob.c, 0);  // zero-ok: sole feasible randc value
          `checkd(ob.x, 1);
        end
      end
      `checkd(good, 4);
    end

    // RandcOnly: filtered three-value cycles, every call succeeds
    begin
      automatic RandcOnly ro = new;
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
    end

    // AllUnsat: every call fails and reports; values are retained
    begin
      automatic AllUnsat au = new;
      automatic int fails = 0;
      au.srandom(55);
      au.c = 2;
      au.x = 1;
      for (int i = 0; i < 4; ++i) begin
        ok = au.randomize();
        if (ok == 0)++fails;
      end
      `checkd(fails, 4);
      `checkd(au.c, 2);
      `checkd(au.x, 1);
    end

    // Top: dotted-path randc, the same cycles through a global constraint
    begin
      automatic Top tp = new;
      automatic int good = 0;
      automatic int tcount[4] = '{default: 0};
      tp.srandom(77);
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
    end

    // RandcHex: 12-value domain, one full cycle, every call succeeds
    begin
      automatic RandcHex rh = new;
      automatic int good = 0;
      automatic int fails = 0;
      automatic bit [15:0] seenHex = 16'b0;
      rh.srandom(88);
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
    end

    // RandcUnsat: no randc value at all, so every call reports and retains
    begin
      automatic RandcUnsat ru = new;
      automatic int fails = 0;
      ru.srandom(99);
      ru.c = 2;
      for (int i = 0; i < 3; ++i) begin
        ok = ru.randomize();
        if (ok == 0)++fails;
      end
      `checkd(fails, 3);
      `checkd(ru.c, 2);
    end

    // PhasedUnsat: the dead domain surfaces in the draw, ahead of the layers
    begin
      automatic PhasedUnsat pu = new;
      automatic int fails = 0;
      pu.srandom(111);
      pu.c = 2;
      for (int i = 0; i < 3; ++i) begin
        ok = pu.randomize();
        if (ok == 0)++fails;
      end
      `checkd(fails, 3);
      `checkd(pu.c, 2);
    end

    // PhasedAllUnsat: drawn value fails and no other value would do better
    begin
      automatic PhasedAllUnsat pa = new;
      automatic int fails = 0;
      pa.srandom(122);
      pa.c = 3;
      for (int i = 0; i < 3; ++i) begin
        ok = pa.randomize();
        if (ok == 0)++fails;
      end
      `checkd(fails, 3);
      `checkd(pa.c, 3);
    end

    // OneCycling: the unconstrained randc member does not disturb c's cycles
    begin
      automatic OneCycling one = new;
      automatic int good = 0;
      automatic int onecount[4] = '{default: 0};
      one.srandom(11);
      for (int i = 0; i < 16 && good < 9; ++i) begin
        ok = one.randomize();
        if (ok == 1) begin
          ++good;
          `checkd(one.c < one.x, 1'b1);
          ++onecount[one.c];
        end
      end
      `checkd(good, 9);
      for (int v = 0; v < 3; ++v) `checkd(onecount[v], 3);
      `checkd(onecount[3], 0);  // zero-ok: c == 3 satisfies no x
    end

    // ModeOff: the randc variable stays fixed and still constrains x
    begin
      automatic ModeOff mo = new;
      automatic int good = 0;
      automatic int fails = 0;
      mo.srandom(133);
      mo.c = 1;
      void'(mo.c.rand_mode(0));
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
    end

    // ModeOffRand: x fixed at 2 makes the relation a filter on c, so c cycles
    // through the two values below it and no call fails
    begin
      automatic ModeOffRand mr = new;
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
    end

    // StateBound: the same two-value cycles under a state variable bound
    begin
      automatic StateBound sb = new;
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
    end

    // ArrayRel: the element's value bounds c the way x does in Flat
    begin
      automatic ArrayRel ar = new;
      automatic int good = 0;
      automatic int acount[4] = '{default: 0};
      ar.srandom(177);
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
    end

    // InlineOnly: the with clause reaches the randc draw, so every call succeeds
    begin
      automatic InlineOnly io = new;
      io.srandom(188);
      for (int i = 0; i < 4; ++i) begin
        ok = io.randomize() with {c == 0;};
        `checkd(ok, 1);
        `checkd(io.c, 0);  // zero-ok: sole value the with clause admits
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
