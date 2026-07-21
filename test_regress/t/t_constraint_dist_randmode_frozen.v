// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A frozen dist variable degrades to a membership test (IEEE 1800-2023 18.5.3).
typedef int unsigned uint;

class Base;
  rand uint delay;
  rand uint x;
  constraint delay_c {delay inside {[1 : 100]};}
  function int rd();
    return this.randomize(delay);
  endfunction
endclass

class SingleVals extends Base;
  constraint c {
    x dist {
      5 := 99,
      1000000 := 1
    };
  }
endclass

class RangeVals extends Base;
  constraint c {
    x dist {
      [1 : 10] := 1,
      [1000 : 2000] := 9
    };
  }
endclass

class MixVals extends Base;
  constraint c {
    x dist {
      0 := 1,
      [100 : 200] := 5,
      9999 := 3
    };
  }
endclass

class DistInIf extends Base;
  rand uint sel;
  constraint c {
    sel inside {0, 1};
    if (sel == 1)
    x dist {
      5 := 9,
      70 := 1
    };
    else
    x == 4242;
  }
endclass

class DistInForeach;
  rand uint arr[4];
  constraint c {
    foreach (arr[i])
    arr[i] dist {
      10 := 9,
      20 := 1
    };
  }
endclass

class StaticVar;
  rand uint delay;
  static rand uint sx;
  constraint delay_c {delay inside {[1 : 100]};}
  constraint c {
    sx dist {
      5 := 9,
      70 := 1
    };
  }
  function int rd();
    return this.randomize(delay);
  endfunction
endclass

class StaticPlain;  // non-dist constraint on a frozen static var
  rand uint d;
  static rand uint sy;
  constraint c {sy inside {[10 : 20]};}
endclass

class Sub;
  rand uint x;
endclass

class Holder;
  rand Sub s;
  rand uint delay;
  constraint delay_c {delay inside {[1 : 100]};}
  constraint c {
    s.x dist {
      5 := 9,
      70 := 1
    };
  }
  function new();
    s = new;
  endfunction
endclass

class MultiVar;
  rand uint x, y;
  constraint c {
    (x + y) dist {
      10 := 9,
      1000 := 1
    };
  }
endclass

class DupVar;
  rand uint x;
  constraint c {
    (x + x) dist {
      10 := 9,
      20 := 1
    };
  }
endclass

class DupMember;
  rand Sub s;
  constraint c {
    (s.x + s.x) dist {
      10 := 9,
      20 := 1
    };
  }
  function new();
    s = new;
  endfunction
endclass

class RtWeight;
  rand uint x;
  uint w;
  constraint c {
    x dist {
      5 := 9,
      70 := w
    };
  }
endclass

class IdxSel;
  rand uint a[4];
  rand uint idx;
  constraint ci {idx inside {[0 : 3]};}
  constraint c {
    a[idx] dist {
      10 := 9,
      20 := 1
    };
  }
endclass

class ConstOp;
  rand uint x;
  constraint c {
    (x + 1) dist {
      6 := 9,
      71 := 1
    };
  }
endclass

class StateMix;
  rand uint x;
  uint nw;
  constraint c {
    (x + nw) dist {
      5 := 9,
      70 := 1
    };
  }
endclass

class MixedFreeze;
  rand uint x, z;
  constraint c {
    (x + z) dist {
      10 := 9,
      1000 := 1
    };
  }
endclass

class NoModeHandle;
  rand Sub s2;
  constraint c {
    s2.x dist {
      5 := 9,
      70 := 1
    };
  }
  function new();
    s2 = new;
  endfunction
endclass

class SelOp;
  rand uint x;
  constraint c {
    x[15:0] dist {
      16'd5 := 9,
      16'd70 := 1
    };
  }
endclass

class NotOp;
  rand uint x;
  constraint c {
    (~x) dist {
      32'hFFFF_FFFA := 9,
      32'hFFFF_FFB9 := 1
    };
  }
endclass

class CondSel;
  rand uint x, y;
  rand bit b;
  constraint c {
    (b ? x : y) dist {
      5 := 9,
      70 := 1
    };
  }
endclass

class ObjArr;
  rand Sub arr2[2];
  constraint c {
    arr2[0].x dist {
      5 := 9,
      70 := 1
    };
  }
  function new();
    arr2[0] = new;
    arr2[1] = new;
  endfunction
endclass

// Same SV shape as CondSel, but x2/y2 never use rand_mode anywhere in this
// test: the arm gates fold to a constant at verilation instead of runtime bits.
class CondSame;
  rand uint x2, y2;
  rand bit b2;
  constraint c {
    (b2 ? x2 : y2) dist {
      5 := 9,
      70 := 1
    };
  }
endclass

typedef struct packed {
  bit [15:0] a;
  bit [15:0] b;
} ab_t;

class PackedStruct;
  rand ab_t st;
  constraint c {
    st.a dist {
      16'd5 := 9,
      16'd70 := 1
    };
  }
endclass

class Mixed;
  rand uint d;
  uint nf;
endclass

class NonRandMember;
  rand Mixed m;
  constraint c {
    m.nf dist {
      5 := 9,
      70 := 1
    };
  }
  function new();
    m = new;
  endfunction
endclass

class QSel;
  rand Sub q[$];
  int pick;
  constraint c {
    q[pick].x dist {
      30 := 9,
      90 := 1
    };
  }
  function new();
    Sub tmp = new;
    q.push_back(tmp);
  endfunction
endclass

module t;
  int ok;
  initial begin
    SingleVals sv;
    RangeVals rv;
    MixVals mv;
    StaticVar st;
    Holder h;
    MultiVar m;
    RtWeight r;
    DistInIf di;
    DistInForeach df;
    IdxSel ix;

    // Frozen in the low-weight bucket -> succeeds, value untouched.
    sv = new;
    ok = sv.randomize();
    `checkd(ok, 1);
    sv.x.rand_mode(0);
    sv.x = 1000000;
    for (int i = 0; i < 8; ++i) begin
      ok = sv.rd();
      `checkd(ok, 1);
      `checkd(sv.x, 1000000);
      if (sv.delay < 1 || sv.delay > 100) $stop;
    end

    // Frozen in the high-weight bucket -> succeeds.
    sv = new;
    ok = sv.randomize();
    `checkd(ok, 1);
    sv.x.rand_mode(0);
    sv.x = 5;
    for (int i = 0; i < 8; ++i) begin
      ok = sv.rd();
      `checkd(ok, 1);
      `checkd(sv.x, 5);
    end

    // Frozen OUTSIDE the set -> membership violated, randomize fails every call.
    sv = new;
    ok = sv.randomize();
    `checkd(ok, 1);
    sv.x.rand_mode(0);
    sv.x = 7;
    for (int i = 0; i < 8; ++i) begin
      ok = sv.rd();
      `checkd(ok, 0);
      `checkd(sv.x, 7);
    end

    // Setting rand_mode back to 1 restores drawing.
    sv.x.rand_mode(1);
    for (int i = 0; i < 8; ++i) begin
      ok = sv.randomize();
      `checkd(ok, 1);
      if (sv.x != 5 && sv.x != 1000000) $stop;
    end

    // Frozen inside a range bucket -> succeeds.
    rv = new;
    ok = rv.randomize();
    `checkd(ok, 1);
    rv.x.rand_mode(0);
    rv.x = 5;
    for (int i = 0; i < 8; ++i) begin
      ok = rv.rd();
      `checkd(ok, 1);
      `checkd(rv.x, 5);
    end

    // Frozen inside a mixed single+range set -> succeeds.
    mv = new;
    ok = mv.randomize();
    `checkd(ok, 1);
    mv.x.rand_mode(0);
    mv.x = 150;
    for (int i = 0; i < 8; ++i) begin
      ok = mv.rd();
      `checkd(ok, 1);
      `checkd(mv.x, 150);
    end

    // Active dist var still solves weighted toward the heavy bucket.
    sv = new;
    begin
      automatic int n5 = 0, nbig = 0;
      for (int i = 0; i < 64; ++i) begin
        ok = sv.randomize();
        `checkd(ok, 1);
        if (sv.x == 5) n5++;
        else if (sv.x == 1000000) nbig++;
        else $stop;
      end
      if (n5 <= nbig) $stop;
    end

    // Static rand var frozen in the low-weight bucket -> succeeds.
    st = new;
    ok = st.randomize();
    `checkd(ok, 1);
    st.sx.rand_mode(0);
    st.sx = 70;
    for (int i = 0; i < 8; ++i) begin
      ok = st.rd();
      `checkd(ok, 1);
      `checkd(st.sx, 70);
      ok = st.randomize();
      `checkd(ok, 1);
      `checkd(st.sx, 70);
    end

    // Static rand var frozen outside the set -> fails every call.
    st.sx = 7;
    for (int i = 0; i < 8; ++i) begin
      ok = st.randomize();
      `checkd(ok, 0);
      `checkd(st.sx, 7);
    end

    // Unfreezing the static var restores drawing.
    st.sx.rand_mode(1);
    for (int i = 0; i < 8; ++i) begin
      ok = st.randomize();
      `checkd(ok, 1);
      if (st.sx != 5 && st.sx != 70) $stop;
    end

    // Frozen static var under a plain constraint: current value decides.
    begin
      StaticPlain sp;
      sp = new;
      ok = sp.randomize();
      `checkd(ok, 1);
      sp.sy.rand_mode(0);
      sp.sy = 15;
      for (int i = 0; i < 8; ++i) begin
        ok = sp.randomize();
        `checkd(ok, 1);
        `checkd(sp.sy, 15);
      end
      sp.sy = 99;
      for (int i = 0; i < 8; ++i) begin
        ok = sp.randomize();
        `checkd(ok, 0);
        `checkd(sp.sy, 99);
      end
    end

    // Sub-object member frozen in the low-weight bucket -> succeeds.
    h = new;
    ok = h.randomize();
    `checkd(ok, 1);
    h.s.x.rand_mode(0);
    h.s.x = 70;
    for (int i = 0; i < 8; ++i) begin
      ok = h.randomize();
      `checkd(ok, 1);
      `checkd(h.s.x, 70);
    end

    // Sub-object member frozen outside the set -> fails every call.
    h.s.x = 7;
    for (int i = 0; i < 8; ++i) begin
      ok = h.randomize();
      `checkd(ok, 0);
      `checkd(h.s.x, 7);
    end

    // Unfreezing the sub-object member restores drawing.
    h.s.x.rand_mode(1);
    for (int i = 0; i < 8; ++i) begin
      ok = h.randomize();
      `checkd(ok, 1);
      if (h.s.x != 5 && h.s.x != 70) $stop;
    end

    // Both the handle and the member frozen.
    h = new;
    ok = h.randomize();
    `checkd(ok, 1);
    h.s.rand_mode(0);
    h.s.x.rand_mode(0);
    h.s.x = 5;
    for (int i = 0; i < 8; ++i) begin
      ok = h.randomize();
      `checkd(ok, 1);
      `checkd(h.s.x, 5);
    end
    h.s.x = 7;
    for (int i = 0; i < 8; ++i) begin
      ok = h.randomize();
      `checkd(ok, 0);
      `checkd(h.s.x, 7);
    end

    // Multi-var dist expression, one var frozen: the active var must still
    // satisfy membership (sum wraps mod 2**32, so both values stay reachable).
    m = new;
    ok = m.randomize();
    `checkd(ok, 1);
    m.x.rand_mode(0);
    m.x = 600;
    for (int i = 0; i < 8; ++i) begin
      ok = m.randomize();
      `checkd(ok, 1);
      `checkd(m.x, 600);
      if (m.x + m.y != 10 && m.x + m.y != 1000) $stop;
    end

    // Both vars frozen: membership of the frozen sum decides.
    m.y.rand_mode(0);
    m.y = 400;
    ok = m.randomize();
    `checkd(ok, 1);
    m.y = 500;
    for (int i = 0; i < 8; ++i) begin
      ok = m.randomize();
      `checkd(ok, 0);
      `checkd(m.y, 500);
    end

    // Same var twice in the dist expression, frozen: membership of 2*x decides.
    begin
      DupVar d;
      d = new;
      ok = d.randomize();
      `checkd(ok, 1);
      d.x.rand_mode(0);
      d.x = 5;
      for (int i = 0; i < 8; ++i) begin
        ok = d.randomize();
        `checkd(ok, 1);
        `checkd(d.x, 5);
      end
      d.x = 7;
      for (int i = 0; i < 8; ++i) begin
        ok = d.randomize();
        `checkd(ok, 0);
        `checkd(d.x, 7);
      end
    end

    // Same sub-object member twice in the dist expression, frozen.
    begin
      DupMember dm;
      dm = new;
      ok = dm.randomize();
      `checkd(ok, 1);
      dm.s.x.rand_mode(0);
      dm.s.x = 5;
      for (int i = 0; i < 8; ++i) begin
        ok = dm.randomize();
        `checkd(ok, 1);
        `checkd(dm.s.x, 5);
      end
      dm.s.x = 7;
      for (int i = 0; i < 8; ++i) begin
        ok = dm.randomize();
        `checkd(ok, 0);
        `checkd(dm.s.x, 7);
      end
    end

    // Runtime weight of zero excludes the bucket's values (18.5.3): frozen
    // there must fail; nonzero weight on the same frozen value succeeds.
    r = new;
    r.w = 1;
    ok = r.randomize();
    `checkd(ok, 1);
    r.x.rand_mode(0);
    r.x = 70;
    for (int i = 0; i < 8; ++i) begin
      ok = r.randomize();
      `checkd(ok, 1);
      `checkd(r.x, 70);
    end
    r.w = 0;
    for (int i = 0; i < 8; ++i) begin
      ok = r.randomize();
      `checkd(ok, 0);
      `checkd(r.x, 70);
    end

    // Active var with a runtime-zero weight never draws that bucket.
    r = new;
    r.w = 0;
    for (int i = 0; i < 8; ++i) begin
      ok = r.randomize();
      `checkd(ok, 1);
      `checkd(r.x, 5);
    end

    // dist inside a constraint if: taken branch follows the dist, else pins 4242.
    di = new;
    for (int i = 0; i < 16; ++i) begin
      ok = di.randomize();
      `checkd(ok, 1);
      if (di.sel == 1) begin
        if (di.x != 5 && di.x != 70) $stop;
      end
      else begin
        `checkd(di.x, 4242);
      end
    end

    // Frozen x forces the solver to whichever branch its value satisfies.
    di.x.rand_mode(0);
    di.x = 70;
    for (int i = 0; i < 8; ++i) begin
      ok = di.randomize();
      `checkd(ok, 1);
      `checkd(di.sel, 1);
      `checkd(di.x, 70);
    end
    di.x = 4242;
    for (int i = 0; i < 8; ++i) begin
      ok = di.randomize();
      `checkd(ok, 1);
      `checkd(di.sel, 0);
      `checkd(di.x, 4242);
    end
    di.x = 7;
    for (int i = 0; i < 8; ++i) begin
      ok = di.randomize();
      `checkd(ok, 0);
      `checkd(di.x, 7);
    end

    // dist inside a constraint foreach: every element honors the set.
    df = new;
    for (int i = 0; i < 16; ++i) begin
      ok = df.randomize();
      `checkd(ok, 1);
      foreach (df.arr[j]) if (df.arr[j] != 10 && df.arr[j] != 20) $stop;
    end

    // Frozen index into an active array: a[idx] still draws BOTH values,
    // biased toward the heavy bucket.
    ix = new;
    ok = ix.randomize();
    `checkd(ok, 1);
    ix.idx.rand_mode(0);
    ix.idx = 2;
    begin
      automatic int n10 = 0, n20 = 0;
      for (int i = 0; i < 64; ++i) begin
        ok = ix.randomize();
        `checkd(ok, 1);
        `checkd(ix.idx, 2);
        if (ix.a[2] == 10) n10++;
        else if (ix.a[2] == 20) n20++;
        else $stop;
      end
      if (n10 == 0 || n20 == 0) $stop;
      if (n10 <= n20) $stop;
    end

    // Constant operand: frozen (x + 1) follows membership of the sum.
    begin
      ConstOp cp;
      cp = new;
      ok = cp.randomize();
      `checkd(ok, 1);
      if (cp.x != 5 && cp.x != 70) $stop;
      cp.x.rand_mode(0);
      cp.x = 70;
      for (int i = 0; i < 8; ++i) begin
        ok = cp.randomize();
        `checkd(ok, 1);
        `checkd(cp.x, 70);
      end
      cp.x = 7;
      for (int i = 0; i < 8; ++i) begin
        ok = cp.randomize();
        `checkd(ok, 0);
        `checkd(cp.x, 7);
      end
    end

    // Non-rand term in the dist expression: only the rand var gates, and the
    // state value participates in the frozen membership.
    begin
      StateMix sm;
      sm = new;
      sm.nw = 0;
      ok = sm.randomize();
      `checkd(ok, 1);
      if (sm.x != 5 && sm.x != 70) $stop;
      sm.x.rand_mode(0);
      sm.x = 70;
      for (int i = 0; i < 8; ++i) begin
        ok = sm.randomize();
        `checkd(ok, 1);
        `checkd(sm.x, 70);
      end
      sm.x = 7;
      for (int i = 0; i < 8; ++i) begin
        ok = sm.randomize();
        `checkd(ok, 0);
        `checkd(sm.x, 7);
      end
      sm.nw = 65;
      sm.x = 5;
      ok = sm.randomize();
      `checkd(ok, 1);
      `checkd(sm.x, 5);
      sm.nw = 66;
      ok = sm.randomize();
      `checkd(ok, 0);
      `checkd(sm.x, 5);
    end

    // Partner var never uses rand_mode: freezing x leaves the dist weighted.
    begin
      MixedFreeze mf;
      mf = new;
      ok = mf.randomize();
      `checkd(ok, 1);
      mf.x.rand_mode(0);
      mf.x = 600;
      begin
        automatic int n10 = 0, n1000 = 0;
        for (int i = 0; i < 64; ++i) begin
          ok = mf.randomize();
          `checkd(ok, 1);
          `checkd(mf.x, 600);
          if (mf.x + mf.z == 10) n10++;
          else if (mf.x + mf.z == 1000) n1000++;
          else $stop;
        end
        if (n10 == 0 || n1000 == 0) $stop;
        if (n10 <= n1000) $stop;
      end
    end

    // Handle without rand_mode in the chain: the member's own bit still gates.
    begin
      NoModeHandle nm;
      nm = new;
      ok = nm.randomize();
      `checkd(ok, 1);
      nm.s2.x.rand_mode(0);
      nm.s2.x = 70;
      for (int i = 0; i < 8; ++i) begin
        ok = nm.randomize();
        `checkd(ok, 1);
        `checkd(nm.s2.x, 70);
      end
      nm.s2.x = 7;
      for (int i = 0; i < 8; ++i) begin
        ok = nm.randomize();
        `checkd(ok, 0);
        `checkd(nm.s2.x, 7);
      end
    end

    // Bit-select: frozen x degrades to membership of the selection.
    begin
      SelOp se;
      se = new;
      ok = se.randomize();
      `checkd(ok, 1);
      if (se.x[15:0] != 5 && se.x[15:0] != 70) $stop;
      se.x.rand_mode(0);
      se.x = 70;
      for (int i = 0; i < 8; ++i) begin
        ok = se.randomize();
        `checkd(ok, 1);
        `checkd(se.x, 70);
      end
      se.x = 7;
      for (int i = 0; i < 8; ++i) begin
        ok = se.randomize();
        `checkd(ok, 0);
        `checkd(se.x, 7);
      end
    end

    // Unary operand: frozen (~x) follows membership of the inverted value.
    begin
      NotOp nt;
      nt = new;
      ok = nt.randomize();
      `checkd(ok, 1);
      if (nt.x != 5 && nt.x != 70) $stop;
      nt.x.rand_mode(0);
      nt.x = 5;
      for (int i = 0; i < 8; ++i) begin
        ok = nt.randomize();
        `checkd(ok, 1);
        `checkd(nt.x, 5);
      end
      nt.x = 7;
      for (int i = 0; i < 8; ++i) begin
        ok = nt.randomize();
        `checkd(ok, 0);
        `checkd(nt.x, 7);
      end
    end

    // Conditional: frozen selector picks the live arm; a frozen selected arm
    // degrades to membership of the selected value.
    begin
      CondSel cs;
      cs = new;
      for (int i = 0; i < 8; ++i) begin
        ok = cs.randomize();
        `checkd(ok, 1);
        if ((cs.b ? cs.x : cs.y) != 5 && (cs.b ? cs.x : cs.y) != 70) $stop;
      end
      cs.b.rand_mode(0);
      cs.b = 1'b1;
      begin
        automatic int n5 = 0, n70 = 0;
        uint y0;
        automatic bit yvar = 0;
        ok = cs.randomize();
        `checkd(ok, 1);
        y0 = cs.y;
        for (int i = 0; i < 64; ++i) begin
          ok = cs.randomize();
          `checkd(ok, 1);
          `checkd(cs.b, 1'b1);
          if (cs.x == 5) n5++;
          else if (cs.x == 70) n70++;
          else $stop;
          if (cs.y != y0) yvar = 1;
        end
        if (n5 == 0 || n70 == 0) $stop;
        if (n5 <= n70) $stop;
        if (!yvar) $stop;
      end
      cs.x.rand_mode(0);
      cs.x = 70;
      for (int i = 0; i < 8; ++i) begin
        ok = cs.randomize();
        `checkd(ok, 1);
        `checkd(cs.x, 70);
      end
      cs.x = 7;
      for (int i = 0; i < 8; ++i) begin
        ok = cs.randomize();
        `checkd(ok, 0);
        `checkd(cs.x, 7);
      end
    end

    // Conditional with mode-less arms: a frozen selector alone stays weighted.
    begin
      CondSame cq;
      cq = new;
      ok = cq.randomize();
      `checkd(ok, 1);
      cq.b2.rand_mode(0);
      for (int i = 0; i < 8; ++i) begin
        ok = cq.randomize();
        `checkd(ok, 1);
        if ((cq.b2 ? cq.x2 : cq.y2) != 5 && (cq.b2 ? cq.x2 : cq.y2) != 70) $stop;
      end
    end

    // Object-array element dist honors the set.
    begin
      ObjArr oa;
      oa = new;
      for (int i = 0; i < 8; ++i) begin
        ok = oa.randomize();
        `checkd(ok, 1);
        if (oa.arr2[0].x != 5 && oa.arr2[0].x != 70) $stop;
      end
    end

    // Packed struct member: frozen struct follows membership of the field.
    begin
      PackedStruct ps;
      ps = new;
      ok = ps.randomize();
      `checkd(ok, 1);
      if (ps.st.a != 5 && ps.st.a != 70) $stop;
      ps.st.rand_mode(0);
      ps.st = '{a: 16'd70, b: 16'd0};
      for (int i = 0; i < 8; ++i) begin
        ok = ps.randomize();
        `checkd(ok, 1);
        `checkd(ps.st.a, 70);
      end
      ps.st = '{a: 16'd7, b: 16'd0};
      for (int i = 0; i < 8; ++i) begin
        ok = ps.randomize();
        `checkd(ok, 0);
        `checkd(ps.st.a, 7);
      end
    end

    // Dist on a non-rand member of a rand object: in-set value succeeds.
    begin
      NonRandMember nr;
      nr = new;
      nr.m.nf = 5;
      ok = nr.randomize();
      `checkd(ok, 1);
      `checkd(nr.m.nf, 5);
    end

    // Queue element member: draws both values, biased toward the heavy bucket.
    begin
      QSel qs;
      qs = new;
      begin
        automatic int n30 = 0, n90 = 0;
        for (int i = 0; i < 64; ++i) begin
          ok = qs.randomize();
          `checkd(ok, 1);
          if (qs.q[0].x == 30) n30++;
          else if (qs.q[0].x == 90) n90++;
          else $stop;
        end
        if (n30 == 0 || n90 == 0) $stop;
        if (n30 <= n90) $stop;
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
