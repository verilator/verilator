// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test: pre/post_randomize callbacks on nested rand class objects and inherited methods
// Covers: IEEE 1800-2023 18.4.1 recursive callback invocation

// --- Inherited callbacks (no override) ---

class BaseInherit;
  rand int x;
  int pre_count;
  int post_count;

  function new();
    pre_count = 0;
    post_count = 0;
  endfunction

  function void pre_randomize;
    pre_count++;
  endfunction

  function void post_randomize;
    post_count++;
  endfunction
endclass

class DerivedNoOverride extends BaseInherit;
  rand int y;

  function new();
    super.new();
  endfunction
  // Does NOT override pre/post_randomize
endclass

class DerivedPartialOverride extends BaseInherit;
  rand int z;
  int derived_pre_count;

  function new();
    super.new();
    derived_pre_count = 0;
  endfunction

  function void pre_randomize;
    derived_pre_count++;
    super.pre_randomize();
  endfunction
  // Does NOT override post_randomize
endclass

// Override both without calling super
class DerivedOverrideBoth extends BaseInherit;
  rand int w;
  int derived_pre_count;
  int derived_post_count;

  function new();
    super.new();
    derived_pre_count = 0;
    derived_post_count = 0;
  endfunction

  function void pre_randomize;
    derived_pre_count++;
  endfunction

  function void post_randomize;
    derived_post_count++;
  endfunction
endclass

// Override only post_randomize without calling super
class DerivedOverridePostOnly extends BaseInherit;
  rand int v;
  int derived_post_count;

  function new();
    super.new();
    derived_post_count = 0;
  endfunction

  // Does NOT override pre_randomize -> should inherit BaseInherit's
  function void post_randomize;
    derived_post_count++;
  endfunction
endclass

// --- Nested rand class callbacks (3-level) ---

class Level3;
  rand bit [7:0] val;
  int pre_count;
  int post_count;

  constraint c_val {val inside {[10 : 200]};}

  function new();
    pre_count = 0;
    post_count = 0;
  endfunction

  function void pre_randomize;
    pre_count++;
  endfunction

  function void post_randomize;
    post_count++;
  endfunction
endclass

class Level2;
  rand Level3 l3;
  rand bit [7:0] val;
  int pre_count;
  int post_count;

  constraint c_val {val inside {[1 : 100]};}

  function new();
    l3 = new();
    pre_count = 0;
    post_count = 0;
  endfunction

  function void pre_randomize;
    pre_count++;
  endfunction

  function void post_randomize;
    post_count++;
  endfunction
endclass

class Level1;
  rand Level2 l2;
  rand bit [7:0] val;
  int pre_count;
  int post_count;

  constraint c_val {val inside {[50 : 150]};}

  function new();
    l2 = new();
    pre_count = 0;
    post_count = 0;
  endfunction

  function void pre_randomize;
    pre_count++;
  endfunction

  function void post_randomize;
    post_count++;
  endfunction
endclass

// --- Cycles of rand class handles (#9063) ---

typedef class CycB;

class CycA;
  rand CycB b;
  int pre_count;
  function void pre_randomize;
    pre_count++;
  endfunction
endclass

class CycB;
  rand CycA a;
  int pre_count;
  function void pre_randomize;
    pre_count++;
  endfunction
endclass

typedef class CycDerivedA;

class CycBase;
  rand CycDerivedA a;
endclass

class CycDerived extends CycBase;
endclass

class CycDerivedA;
  rand CycDerived b;
endclass

// --- No post_randomize when randomize() fails (#8881) ---

class FailInner;
  rand bit [14:0] p;
  int post_count;
  function void post_randomize;
    post_count++;
  endfunction
endclass

class FailOuter;
  rand bit [6:0] c;
  rand FailInner inner;
  int post_count;
  constraint bad {
    c > 100;
    c < 50;
  }
  function new();
    inner = new;
  endfunction
  function void post_randomize;
    post_count++;
  endfunction
endclass

class FailBase;
  rand bit [6:0] c;
endclass

class FailDerived extends FailBase;
  int post_count;
  function void post_randomize;
    post_count++;
  endfunction
endclass

module t;

  initial begin
    automatic int r;

    // Test: Inherited callbacks (no override)
    begin
      automatic DerivedNoOverride obj = new;
      r = obj.randomize();
      `checkd(r, 1);
      `checkd(obj.pre_count, 1);
      `checkd(obj.post_count, 1);
    end

    // Test: Partial override (pre overridden, post inherited)
    begin
      automatic DerivedPartialOverride obj = new;
      r = obj.randomize();
      `checkd(r, 1);
      `checkd(obj.derived_pre_count, 1);
      `checkd(obj.pre_count, 1);  // super.pre_randomize called
      `checkd(obj.post_count, 1);  // inherited post_randomize
    end

    // Test: Override both without super - base counts stay 0
    begin
      automatic DerivedOverrideBoth obj = new;
      r = obj.randomize();
      `checkd(r, 1);
      `checkd(obj.derived_pre_count, 1);
      `checkd(obj.derived_post_count, 1);
      `checkd(obj.pre_count, 0);  // base NOT called (no super)
      `checkd(obj.post_count, 0);  // base NOT called (no super)
    end

    // Test: Override only post, inherit pre
    begin
      automatic DerivedOverridePostOnly obj = new;
      r = obj.randomize();
      `checkd(r, 1);
      `checkd(obj.pre_count, 1);  // inherited pre_randomize called
      `checkd(obj.derived_post_count, 1);  // overridden post called
      `checkd(obj.post_count, 0);  // base post NOT called (no super)
    end

    // Test: Nested callbacks (3-level)
    begin
      automatic Level1 l1 = new;
      r = l1.randomize();
      `checkd(r, 1);
      `checkd(l1.pre_count, 1);
      `checkd(l1.post_count, 1);
      `checkd(l1.l2.pre_count, 1);
      `checkd(l1.l2.post_count, 1);
      `checkd(l1.l2.l3.pre_count, 1);
      `checkd(l1.l2.l3.post_count, 1);
    end

    // Test: Multiple randomizations
    begin
      automatic Level1 l1 = new;
      repeat (5) begin
        r = l1.randomize();
        `checkd(r, 1);
      end
      `checkd(l1.pre_count, 5);
      `checkd(l1.post_count, 5);
      `checkd(l1.l2.pre_count, 5);
      `checkd(l1.l2.post_count, 5);
      `checkd(l1.l2.l3.pre_count, 5);
      `checkd(l1.l2.l3.post_count, 5);
    end

    // Test: Cycle of rand class handles
    begin
      automatic CycA a = new;
      r = a.randomize();
      `checkd(r, 1);
      `checkd(a.pre_count, 1);
    end

    // Test: Cycle of rand class handles through a base class
    begin
      automatic CycDerivedA a = new;
      r = a.randomize();
      `checkd(r, 1);
    end

    // Test: post_randomize is not called when randomize() fails (IEEE 18.6.3)
    begin
      automatic FailOuter obj = new;
      r = obj.randomize();
      `checkd(r, 0);
      r = obj.randomize() with {c == 1;};
      `checkd(r, 0);
      `checkd(obj.post_count, 0);
      `checkd(obj.inner.post_count, 0);
    end

    // Test: virtual post_randomize through base handle only on success
    begin
      automatic FailDerived d = new;
      automatic FailBase b = d;
      r = b.randomize() with {
        c > 100;
        c < 50;
      };
      `checkd(r, 0);
      `checkd(d.post_count, 0);
      r = b.randomize() with {c == 5;};
      `checkd(r, 1);
      `checkd(d.post_count, 1);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
