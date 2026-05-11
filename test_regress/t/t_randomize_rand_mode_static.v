// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

// Tests rand_mode() support for `static rand` class members per IEEE 1800-2023
// Section 18.5.10 and Section 18.4. Static rand_mode state is shared across all
// instances of a class.

class Simple;
  static rand int sx;
  rand int dy;
  constraint c {
    sx > 0;
    sx < 12;
    dy > 100;
    dy < 200;
  }
endclass

class Base;
  static rand bit [3:0] base_sx;
  rand bit [3:0] base_dy;
  constraint base_c {
    base_sx > 0;
    base_dy > 0;
  }
endclass

class Derived extends Base;
  rand bit [3:0] der_dy;
  constraint der_c {der_dy > 0;}
endclass

// Class with ONLY static rand members; exercises class-level rand_mode() with
// no per-instance mode array.
class StaticOnly;
  static rand bit [3:0] sa;
  static rand bit [3:0] sb;
  constraint c {
    sa > 0;
    sb > 0;
  }
endclass

// Base with two static rand vars exercises non-zero index in the shared static array.
class BaseTwo;
  static rand bit [3:0] base2_a;
  static rand bit [3:0] base2_b;
  rand bit [3:0] base2_dy;
  constraint c {
    base2_a > 0;
    base2_b > 0;
    base2_dy > 0;
  }
endclass

class DerivedTwo extends BaseTwo;
  rand bit [3:0] der2_dy;
  constraint dc {der2_dy > 0;}
endclass

// No constraint blocks: inline randomize-with must still flush static rand_mode.
class StaticNoConstraint;
  static rand bit [3:0] snc_s;
  rand bit [3:0] snc_d;
endclass

// Base + Derived each declare a static rand var; per-root max-count init must size for both.
class BaseS;
  static rand bit [3:0] base_s;
  constraint c {base_s > 0;}
endclass

class DerivedS extends BaseS;
  static rand bit [3:0] der_s;
  constraint c2 {der_s > 0;}
endclass

module t;
  Simple s1, s2;
  Derived d1, d2;
  StaticOnly so1, so2;
  BaseS bs1;
  DerivedS ds1, ds2;
  DerivedTwo dt1;
  StaticNoConstraint snc1;
  int saved_sx, saved_dy, rok;
  bit [3:0] saved_base_sx, saved_base_s, saved_der_s, saved_base2_b;

  initial begin
    s1 = new;
    s2 = new;

    // ---- Test 1: getter on static rand var (initial state is enabled)
    `checkd(s1.sx.rand_mode(), 1);
    `checkd(s2.sx.rand_mode(), 1);

    // ---- Test 2: randomize() with all rand_modes enabled satisfies constraints
    repeat (20) begin
      rok = s1.randomize();
      `checkd(rok, 1);
      `check_range(Simple::sx, 1, 11);
      `check_range(s1.dy, 101, 199);
    end

    // ---- Test 3: per-member set on a static rand var is shared across instances
    s1.sx.rand_mode(0);
    `checkd(s1.sx.rand_mode(), 0);
    `checkd(s2.sx.rand_mode(), 0);

    // Non-static dy stays independent on each instance
    `checkd(s1.dy.rand_mode(), 1);
    `checkd(s2.dy.rand_mode(), 1);

    // ---- Test 4: solver respects rand_mode(0) on static rand var.
    // sx is currently a valid value from Test 2; with rand_mode disabled it
    // must stay at that value across multiple randomize() calls.
    saved_sx = Simple::sx;
    repeat (20) begin
      rok = s1.randomize();
      `checkd(rok, 1);
      `checkd(Simple::sx, saved_sx);
      `check_range(s1.dy, 101, 199);
    end

    // Re-enable rand_mode for sx via the OTHER instance (sharing test).
    s2.sx.rand_mode(1);
    `checkd(s1.sx.rand_mode(), 1);

    repeat (20) begin
      rok = s1.randomize();
      `checkd(rok, 1);
      `check_range(Simple::sx, 1, 11);
      `check_range(s1.dy, 101, 199);
    end

    // ---- Test 5: class-level obj.rand_mode(0) flushes both per-instance
    // and static arrays. Disable everything on s1.
    s1.rand_mode(0);
    `checkd(s1.sx.rand_mode(), 0);
    `checkd(s1.dy.rand_mode(), 0);
    // Static sx is shared, so s2 sees it disabled too.
    `checkd(s2.sx.rand_mode(), 0);
    // Non-static dy on s2 is independent of s1's class-level call.
    `checkd(s2.dy.rand_mode(), 1);

    // Re-randomize s1 with everything off - both fields unchanged.
    saved_sx = Simple::sx;
    saved_dy = s1.dy;
    repeat (10) begin
      rok = s1.randomize();
      `checkd(rok, 1);
      `checkd(Simple::sx, saved_sx);
      `checkd(s1.dy, saved_dy);
    end

    // Class-level enable resets both arrays to 1.
    s1.rand_mode(1);
    `checkd(s1.sx.rand_mode(), 1);
    `checkd(s1.dy.rand_mode(), 1);
    `checkd(s2.sx.rand_mode(), 1);

    // ---- Test 6: inheritance - static rand var declared in base class,
    // accessed via a derived-class instance.
    d1 = new;
    d2 = new;

    `checkd(d1.base_sx.rand_mode(), 1);

    // Randomize first so base_sx satisfies its constraint, then disable it.
    rok = d1.randomize();
    `checkd(rok, 1);
    if (Base::base_sx == 0) $stop;

    d1.base_sx.rand_mode(0);
    `checkd(d1.base_sx.rand_mode(), 0);
    `checkd(d2.base_sx.rand_mode(), 0);  // Shared via base class

    // Derived class member dy is non-static, independent.
    `checkd(d1.der_dy.rand_mode(), 1);
    `checkd(d2.der_dy.rand_mode(), 1);

    saved_base_sx = Base::base_sx;
    repeat (20) begin
      rok = d1.randomize();
      `checkd(rok, 1);
      `checkd(Base::base_sx, saved_base_sx);  // disabled - unchanged
      if (d1.der_dy == 0) $stop;
      if (d1.base_dy == 0) $stop;
    end

    // ---- Test 7: class-level rand_mode(N) on a class with ONLY static rand members.
    so1 = new;
    so2 = new;
    `checkd(so1.sa.rand_mode(), 1);
    `checkd(so1.sb.rand_mode(), 1);
    so1.rand_mode(0);  // must not crash
    `checkd(so1.sa.rand_mode(), 0);
    `checkd(so1.sb.rand_mode(), 0);
    `checkd(so2.sa.rand_mode(), 0);  // shared
    `checkd(so2.sb.rand_mode(), 0);  // shared
    so2.rand_mode(1);
    `checkd(so1.sa.rand_mode(), 1);
    `checkd(so1.sb.rand_mode(), 1);

    // ---- Test 8: inline obj.randomize(static_var) save/restore.
    // The inline form must route through the static rand_mode array, not
    // the per-instance one (whose index space is different / smaller).
    s1.sx.rand_mode(1);
    s1.dy.rand_mode(1);
    repeat (10) begin
      rok = s1.randomize(sx);  // only sx is randomized, dy frozen
      `checkd(rok, 1);
      `check_range(Simple::sx, 1, 11);
    end
    // After the inline call, s1.sx.rand_mode() must be back to 1
    // (the save/restore restores the static array).
    `checkd(s1.sx.rand_mode(), 1);
    `checkd(s2.sx.rand_mode(), 1);  // shared - also 1

    // ---- Test 9: Base AND Derived each declare own static rand var.
    // Derived's static array must be sized to fit BOTH base_s and der_s
    // even though super.new() runs Base's init first.
    ds1 = new;
    ds2 = new;
    `checkd(ds1.base_s.rand_mode(), 1);
    `checkd(ds1.der_s.rand_mode(), 1);
    rok = ds1.randomize();
    `checkd(rok, 1);
    if (BaseS::base_s == 0) $stop;
    if (DerivedS::der_s == 0) $stop;

    // Disable both via per-member call
    ds1.base_s.rand_mode(0);
    ds1.der_s.rand_mode(0);
    `checkd(ds2.base_s.rand_mode(), 0);  // shared
    `checkd(ds2.der_s.rand_mode(), 0);  // shared
    saved_base_s = BaseS::base_s;
    saved_der_s = DerivedS::der_s;
    repeat (10) begin
      rok = ds1.randomize();
      `checkd(rok, 1);
      `checkd(BaseS::base_s, saved_base_s);
      `checkd(DerivedS::der_s, saved_der_s);
    end

    // Construct a standalone BaseS AFTER DerivedS already initialized the
    // static array; BaseS init must see size != 0 and skip without
    // overwriting Derived's prior rand_mode(0) state.
    bs1 = new;
    `checkd(bs1.base_s.rand_mode(), 0);  // still disabled

    // ---- Test 10: two static rand vars in Base; Derived must accumulate inherited indices.
    dt1 = new;
    `checkd(dt1.base2_a.rand_mode(), 1);
    `checkd(dt1.base2_b.rand_mode(), 1);
    rok = dt1.randomize();
    `checkd(rok, 1);
    if (BaseTwo::base2_a == 0) $stop;
    if (BaseTwo::base2_b == 0) $stop;
    // Disable second static var to prove its index is reachable in the array.
    dt1.base2_b.rand_mode(0);
    `checkd(dt1.base2_b.rand_mode(), 0);
    `checkd(dt1.base2_a.rand_mode(), 1);  // first still enabled
    saved_base2_b = BaseTwo::base2_b;
    repeat (10) begin
      rok = dt1.randomize();
      `checkd(rok, 1);
      `checkd(BaseTwo::base2_b, saved_base2_b);  // disabled - unchanged
      if (BaseTwo::base2_a == 0) $stop;  // still randomizing
    end

    // ---- Test 11: inline randomize-with on class with static rand and no class-level constraints.
    snc1 = new;
    snc1.snc_s.rand_mode(1);  // ensure static rand-mode array exists
    repeat (10) begin
      rok = snc1.randomize() with {
        snc_d > 5;
        snc_d < 13;
      };
      `checkd(rok, 1);
      `check_range(snc1.snc_d, 6, 12);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
