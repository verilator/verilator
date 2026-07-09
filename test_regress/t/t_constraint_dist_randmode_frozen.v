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
  constraint delay_c {delay inside {[1:100]};}
  function int rd();
    return this.randomize(delay);
  endfunction
endclass

class SingleVals extends Base;
  constraint c {x dist {5 := 99, 1000000 := 1};}
endclass

class RangeVals extends Base;
  constraint c {x dist {[1:10] := 1, [1000:2000] := 9};}
endclass

class MixVals extends Base;
  constraint c {x dist {0 := 1, [100:200] := 5, 9999 := 3};}
endclass

class DistInIf extends Base;
  rand uint sel;
  constraint c {
    sel inside {0, 1};
    if (sel == 1) x dist {5 := 9, 70 := 1};
    else x == 4242;
  }
endclass

class DistInForeach;
  rand uint arr[4];
  constraint c {foreach (arr[i]) arr[i] dist {10 := 9, 20 := 1};}
endclass

class StaticVar;
  rand uint delay;
  static rand uint sx;
  constraint delay_c {delay inside {[1:100]};}
  constraint c {sx dist {5 := 9, 70 := 1};}
  function int rd();
    return this.randomize(delay);
  endfunction
endclass

class StaticPlain;  // non-dist constraint on a frozen static var
  rand uint d;
  static rand uint sy;
  constraint c {sy inside {[10:20]};}
endclass

class Sub;
  rand uint x;
endclass

class Holder;
  rand Sub s;
  rand uint delay;
  constraint delay_c {delay inside {[1:100]};}
  constraint c {s.x dist {5 := 9, 70 := 1};}
  function new();
    s = new;
  endfunction
endclass

class MultiVar;
  rand uint x, y;
  constraint c {(x + y) dist {10 := 9, 1000 := 1};}
endclass

class DupVar;
  rand uint x;
  constraint c {(x + x) dist {10 := 9, 20 := 1};}
endclass

class DupMember;
  rand Sub s;
  constraint c {(s.x + s.x) dist {10 := 9, 20 := 1};}
  function new();
    s = new;
  endfunction
endclass

class RtWeight;
  rand uint x;
  uint w;
  constraint c {x dist {5 := 9, 70 := w};}
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

    // Active dist var still solves (weighted, never fails on a valid set).
    sv = new;
    for (int i = 0; i < 8; ++i) begin
      ok = sv.randomize();
      `checkd(ok, 1);
      if (sv.x != 5 && sv.x != 1000000) `checkd(0, 1);
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
      if (m.x + m.y != 10 && m.x + m.y != 1000) `checkd(0, 1);
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
        if (di.x != 5 && di.x != 70) `checkd(0, 1);
      end else begin
        `checkd(di.x, 4242);
      end
    end

    // dist inside a constraint foreach: every element honors the set.
    df = new;
    for (int i = 0; i < 16; ++i) begin
      ok = df.randomize();
      `checkd(ok, 1);
      foreach (df.arr[j])
        if (df.arr[j] != 10 && df.arr[j] != 20) `checkd(0, 1);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
