// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// solve...before over array rand variables: each solved layer is pinned
// per element so the phased solve round-trips.
class OneD;
  rand int unsigned a[2];
  rand int unsigned b[2];
  constraint c {
    solve a before b;
    foreach (b[i]) b[i] == a[i] + 1;
  }
endclass

class TwoD;
  rand int unsigned a[2][2];
  rand int unsigned b[2][2];
  constraint c {
    solve a before b;
    foreach (b[i, j]) b[i][j] == a[i][j] + 1;
  }
endclass

class Mul;  // the rv_timer ticks_c shape: mul across a solved layer
  rand int unsigned prescale[2];
  rand int unsigned ticks[2];
  constraint c {
    solve prescale before ticks;
    foreach (ticks[i]) (ticks[i] * (prescale[i] + 1)) <= 5000;
  }
endclass

class Chain;  // three-layer chain
  rand int unsigned a[2];
  rand int unsigned b[2];
  rand int unsigned d[2];
  constraint c {
    solve a before b;
    solve b before d;
    foreach (a[i]) a[i] inside {[1:10]};
    foreach (b[i]) b[i] == a[i] * 2;
    foreach (d[i]) d[i] == b[i] + a[i];
  }
endclass

class Que;  // dynamic container solved before a scalar
  rand int unsigned q[$];
  rand int unsigned s;
  constraint c {
    q.size() == 3;
    solve q before s;
    foreach (q[i]) q[i] inside {[1:10]};
    s == q[0] + q[1] + q[2];
  }
endclass

class ScFirst;  // scalar solved before an array
  rand int unsigned xw;
  rand int unsigned a[2];
  constraint c {
    solve xw before a;
    xw inside {[1:5]};
    foreach (a[i]) a[i] == xw + i;
  }
endclass

class DynArr;  // dynamic array solved before a scalar
  rand int unsigned d[];
  rand int unsigned s;
  constraint c {
    d.size() == 3;
    solve d before s;
    foreach (d[i]) d[i] inside {[1:10]};
    s == d[0] + d[1] + d[2];
  }
endclass

// Explicit container sizes are valid on either side of solve...before.
class Issue9092;
  rand int unsigned n;
  rand bit [7:0] d[];
  constraint c {
    n inside {[1:4]};
    d.size == n;
    solve n before d.size;
  }
endclass

class SizeAfter;
  rand int unsigned n_before;
  rand bit [7:0] dyn_after[];
  rand bit [7:0] que_after[$];
  constraint c {
    n_before inside {[1:4]};
    dyn_after.size == n_before;
    que_after.size == n_before;
    solve n_before before dyn_after.size, que_after.size;
  }
endclass

class SizeBefore;
  rand int unsigned n_after;
  rand bit [7:0] dyn_before[];
  rand bit [7:0] que_before[$];
  constraint c {
    n_after inside {[1:4]};
    dyn_before.size == n_after;
    que_before.size == n_after;
    solve dyn_before.size, que_before.size before n_after;
  }
endclass

class SizeFixed;
  rand int unsigned n;
  rand bit [7:0] d[];
  rand bit [7:0] q[$];
  constraint c {
    n inside {[1:4]};
    solve n before d.size;
    solve q.size before n;
  }
endclass

class SizeInline;
  rand int unsigned inline_n;
  rand bit [7:0] inline_d[];
  constraint c {
    inline_n inside {[1:4]};
    solve inline_n before inline_d.size;
  }
endclass

class SizeWith;
  rand int unsigned with_n;
  rand bit [7:0] with_d[];
  rand bit [7:0] with_q[$];
endclass

class SizeAssoc;
  rand int unsigned assoc_n;
  rand bit [7:0] assoc[int];
  constraint c {
    assoc_n inside {[1:4]};
    solve assoc_n before assoc.size;
    solve assoc.size before assoc_n;
  }
endclass

class SizeOther;
  rand bit [7:0] path_d[];
endclass

class SizePath;
  rand int unsigned path_n;
  rand bit [7:0] path_d[];
  constraint c {
    path_n inside {[1:4]};
    path_d.size inside {[1:4]};
  }
endclass

class SizeIndependent;
  rand int unsigned first;
  rand int unsigned last;
  rand bit [7:0] d[];
  constraint c {
    solve first before d.size;
    solve d.size before last;
    first inside {[1:3]};
    last inside {[1:3]};
    d.size inside {[1:3]};
  }
endclass

module t;
  initial begin
    Issue9092 original;
    SizeAfter afters;
    SizeBefore befores;
    SizeFixed fixeds;
    SizeInline inliner;
    SizeWith withs;
    SizeAssoc assocs;
    SizeOther other;
    SizePath paths;
    SizeIndependent independent;
    int ok;
    original = new;
    afters = new;
    befores = new;
    fixeds = new;
    fixeds.d = new[3];
    fixeds.q.push_back(1);
    fixeds.q.push_back(2);
    inliner = new;
    withs = new;
    withs.with_d = new[3];
    withs.with_q.push_back(1);
    withs.with_q.push_back(2);
    assocs = new;
    assocs.assoc[7] = 1;
    other = new;
    other.path_d = new[2];
    paths = new;
    independent = new;
    repeat (10) begin
      ok = original.randomize();
      `checkd(ok, 1);
      `checkd(original.d.size(), original.n);
      ok = afters.randomize();
      `checkd(ok, 1);
      `checkd(afters.dyn_after.size(), afters.n_before);
      `checkd(afters.que_after.size(), afters.n_before);
      ok = befores.randomize();
      `checkd(ok, 1);
      `checkd(befores.dyn_before.size(), befores.n_after);
      `checkd(befores.que_before.size(), befores.n_after);
      ok = fixeds.randomize();
      `checkd(ok, 1);
      `checkd(fixeds.d.size(), 3);
      `checkd(fixeds.q.size(), 2);
      ok = inliner.randomize() with { inline_d.size == inline_n; };
      `checkd(ok, 1);
      `checkd(inliner.inline_d.size(), inliner.inline_n);
      withs.with_d = new[3];
      ok = withs.randomize() with {
        with_n inside {[1:4]};
        solve with_n before with_d.size;
        solve with_q.size before with_n;
      };
      `checkd(ok, 1);
      `checkd(withs.with_d.size(), 3);
      `checkd(withs.with_q.size(), 2);
      ok = withs.randomize() with {
        with_n inside {[1:4]};
        with_d.size == with_n;
        solve with_n before with_d.size;
      };
      `checkd(ok, 1);
      `checkd(withs.with_d.size(), withs.with_n);
      ok = assocs.randomize();
      `checkd(ok, 1);
      `checkd(assocs.assoc.num(), 1);
      ok = assocs.randomize() with {
        solve assoc_n before assoc.size;
        solve assoc.size before assoc_n;
      };
      `checkd(ok, 1);
      `checkd(assocs.assoc.num(), 1);
      ok = paths.randomize() with { solve other.path_d.size before path_n; };
      `checkd(ok, 1);
      `checkd(other.path_d.size(), 2);
      ok = independent.randomize();
      `checkd(ok, 1);
      if (independent.d.size() < 1 || independent.d.size() > 3) `stop;
    end
  end

  OneD o1;
  TwoD o2;
  Mul om;
  Chain oc;
  Que oq;
  ScFirst osf;
  DynArr odn;
  int ok;
  initial begin
    o1 = new;
    o2 = new;
    om = new;
    oc = new;
    oq = new;
    osf = new;
    odn = new;
    for (int i = 0; i < 10; ++i) begin
      ok = o1.randomize();
      `checkd(ok, 1);
      `checkd(o1.b[0], o1.a[0] + 1);
      `checkd(o1.b[1], o1.a[1] + 1);

      ok = o2.randomize();
      `checkd(ok, 1);
      `checkd(o2.b[0][0], o2.a[0][0] + 1);
      `checkd(o2.b[1][1], o2.a[1][1] + 1);

      ok = om.randomize();
      `checkd(ok, 1);
      if ((om.ticks[0] * (om.prescale[0] + 1)) > 5000) `checkd(0, 1);

      ok = oc.randomize();
      `checkd(ok, 1);
      `checkd(oc.b[0], oc.a[0] * 2);
      `checkd(oc.d[1], oc.b[1] + oc.a[1]);

      ok = oq.randomize();
      `checkd(ok, 1);
      `checkd(oq.s, oq.q[0] + oq.q[1] + oq.q[2]);

      ok = osf.randomize();
      `checkd(ok, 1);
      `checkd(osf.a[0], osf.xw);
      `checkd(osf.a[1], osf.xw + 1);

      ok = odn.randomize();
      `checkd(ok, 1);
      `checkd(odn.d.size(), 3);
      `checkd(odn.s, odn.d[0] + odn.d[1] + odn.d[2]);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
