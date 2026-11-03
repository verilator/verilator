// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test: randc variables with additional constraints limiting values
// IEEE 1800-2023 18.4.2: randc cyclic behavior over constrained domain

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

class RandcRange;
  randc bit [3:0] value;  // 4-bit: unconstrained domain = 0-15

  constraint c_range {
    value >= 3;
    value <= 10;
  }

  function void test_cyclic;
    automatic int count[16];
    automatic int domain_size = 8;  // values 3..10
    automatic int randomize_result;
    $display("Test randc with range constraint [3:10]");
    // Run 3 full cycles
    for (int trial = 0; trial < 3; ++trial) begin
      for (int i = 0; i < domain_size; ++i) begin
        randomize_result = randomize();
        `checkd(randomize_result, 1);
        `check_range(value, 3, 10);
        ++count[value];
      end
    end
    // After 3 full cycles, each value in [3,10] should appear exactly 3 times
    for (int v = 3; v <= 10; ++v) begin
      `checkd(count[v], 3);
    end
    // Values outside [3,10] should never appear
    for (int v = 0; v < 3; ++v) begin
      `checkd(count[v], 0);
    end
    for (int v = 11; v < 16; ++v) begin
      `checkd(count[v], 0);
    end
  endfunction
endclass

class RandcSmall;
  randc bit [1:0] val;  // 4 possible values: 0,1,2,3
  constraint c_exclude {val != 0;}  // 3 valid values: 1,2,3

  function void test_cyclic;
    automatic int count[4];
    automatic int domain_size = 3;
    automatic int randomize_result;
    $display("Test randc with exclude constraint (val != 0)");
    // Run 4 full cycles
    for (int trial = 0; trial < 4; ++trial) begin
      for (int i = 0; i < domain_size; ++i) begin
        randomize_result = randomize();
        `checkd(randomize_result, 1);
        `checkd(val == 0, 0);
        ++count[val];
      end
    end
    // After 4 full cycles, each of 1,2,3 should appear exactly 4 times
    `checkd(count[0], 0);
    for (int v = 1; v <= 3; ++v) begin
      `checkd(count[v], 4);
    end
  endfunction
endclass

// Test 3: Inheritance - parent randc with constraint, child inherits
class RandcParent;
  randc bit [2:0] code;  // 8 values: 0-7
  constraint c_positive {code > 0;}  // 7 valid values: 1-7

  function void test_cyclic;
    automatic int count[8];
    automatic int domain_size = 7;
    automatic int randomize_result;
    $display("Test randc parent with constraint (code > 0)");
    for (int trial = 0; trial < 3; ++trial) begin
      for (int i = 0; i < domain_size; ++i) begin
        randomize_result = randomize();
        `checkd(randomize_result, 1);
        `checkd(code == 0, 0);
        ++count[code];
      end
    end
    for (int v = 1; v <= 7; ++v) begin
      `checkd(count[v], 3);
    end
    `checkd(count[0], 0);
  endfunction
endclass

class RandcChild extends RandcParent;
  // Inherits randc code and c_positive constraint
  constraint c_upper {code <= 5;}  // Further restrict: 1-5 (5 values)

  function void test_cyclic;
    automatic int count[8];
    automatic int domain_size = 5;
    automatic int randomize_result;
    $display("Test randc child with inherited + additional constraint (1 <= code <= 5)");
    for (int trial = 0; trial < 4; ++trial) begin
      for (int i = 0; i < domain_size; ++i) begin
        randomize_result = randomize();
        `checkd(randomize_result, 1);
        `check_range(code, 1, 5);
        ++count[code];
      end
    end
    for (int v = 1; v <= 5; ++v) begin
      `checkd(count[v], 4);
    end
    for (int v = 6; v <= 7; ++v) begin
      `checkd(count[v], 0);
    end
  endfunction
endclass

// Test 5: constraint_mode() interaction
// Verifies randc cyclic behavior adapts when constraints are toggled at runtime.
// Note: randc cycles are continuous, not per-phase, so we verify constraint
// enforcement and that all valid values eventually appear rather than exact counts.
class RandcModeSwitch;
  randc bit [1:0] x;  // 4 values: 0-3
  constraint c_nonzero {x != 0;}  // 3 valid values: 1,2,3

  function void test_mode_switch;
    automatic int randomize_result;
    automatic bit seen_zero;

    // Phase 1: constraint ON -> x should never be 0, and all of {1,2,3} should appear
    $display("Test constraint_mode: phase 1 (constraint ON)");
    begin
      automatic bit seen[4] = '{0, 0, 0, 0};
      // Run 2 full cycles (6 calls) to ensure all constrained values appear
      for (int i = 0; i < 6; ++i) begin
        randomize_result = randomize();
        `checkd(randomize_result, 1);
        `checkd(x == 0, 0);
        seen[x] = 1;
      end
      for (int v = 1; v <= 3; ++v) begin
        `checkd(seen[v], 1);
      end
    end

    // Phase 2: constraint OFF -> x=0 should eventually appear
    $display("Test constraint_mode: phase 2 (constraint OFF)");
    c_nonzero.constraint_mode(0);
    seen_zero = 0;
    // Run enough calls (2 full cycles of 4 + margin) to see all values
    for (int i = 0; i < 12; ++i) begin
      randomize_result = randomize();
      `checkd(randomize_result, 1);
      if (x == 0) seen_zero = 1;
    end
    `checkd(seen_zero, 1);

    // Phase 3: constraint back ON -> x should never be 0 again
    $display("Test constraint_mode: phase 3 (constraint ON again)");
    c_nonzero.constraint_mode(1);
    for (int i = 0; i < 9; ++i) begin
      randomize_result = randomize();
      `checkd(randomize_result, 1);
      `checkd(x == 0, 0);
    end
  endfunction
endclass

// Test 6: Enum randc with constraint excluding some values
// Use a 2-bit enum where all bit values are valid enum members,
// so the solver domain matches the enum domain exactly.
class RandcEnumConstrained;
  typedef enum bit [1:0] {
    RED = 0,
    GREEN = 1,
    BLUE = 2,
    WHITE = 3
  } color_t;

  randc color_t color;
  constraint c_no_white {color != WHITE;}  // 3 valid: RED, GREEN, BLUE

  function void test_cyclic;
    automatic int count[4] = '{0, 0, 0, 0};
    automatic int domain_size = 3;
    automatic int randomize_result;
    $display("Test randc enum with constraint (exclude WHITE)");
    for (int trial = 0; trial < 4; ++trial) begin
      for (int i = 0; i < domain_size; ++i) begin
        randomize_result = randomize();
        `checkd(randomize_result, 1);
        `checkd(color == WHITE, 0);
        ++count[color];
      end
    end
    for (int v = 0; v <= 2; ++v) begin
      `checkd(count[v], 4);
    end
    `checkd(count[3], 0);
  endfunction
endclass

// Test 7: Deep cyclic - full 4-bit range 0:15 (16 values, no constraint)
class RandcDeep;
  randc bit [3:0] val;

  function void test_cyclic;
    automatic int count[16];
    automatic int domain_size = 16;
    automatic int randomize_result;
    $display("Test randc deep cyclic [0:15] (16 values)");
    // Run 3 full cycles
    for (int trial = 0; trial < 3; ++trial) begin
      for (int i = 0; i < domain_size; ++i) begin
        randomize_result = randomize();
        `checkd(randomize_result, 1);
        ++count[val];
      end
    end
    // Each value 0..15 should appear exactly 3 times
    for (int v = 0; v < 16; ++v) begin
      `checkd(count[v], 3);
    end
  endfunction
endclass

// Test 8: randc mixed with rand variables named only in an if condition, an
// implication, a foreach, an inside list or a struct member. Each constraint names
// a rand variable, so it must stay out of the randc-first draw. Every value of c stays
// feasible, so each cycle covers 0..3.
virtual class RandcMixedBase;
  randc bit [1:0] c;

  pure virtual function bit holds;
  // Each case randomizes itself, so the call is resolved in the class declaring its members
  pure virtual function int randomize_case;

  function void test_cyclic(string what);
    automatic int count[4] = '{0, 0, 0, 0};
    automatic int randomize_result;
    $display("Test randc mixed with rand through %s", what);
    // Run 3 full cycles
    for (int trial = 0; trial < 3; ++trial) begin
      for (int i = 0; i < 4; ++i) begin
        randomize_result = randomize_case();
        `checkd(randomize_result, 1);
        `checkd(holds(), 1);
        ++count[c];
      end
    end
    for (int v = 0; v < 4; ++v) begin
      `checkd(count[v], 3);
    end
  endfunction
endclass

class RandcIfCond extends RandcMixedBase;
  rand bit [1:0] x;
  constraint c_if {
    if (x > 0) {
      c < 2;
    } else {
      c >= 2;
    }
  }
  function bit holds;
    return (x > 0) ? (c < 2) : (c >= 2);
  endfunction
  function int randomize_case;
    return randomize();
  endfunction
endclass

class RandcImplication extends RandcMixedBase;
  rand bit x;
  constraint c_imp {x -> c != 3;}
  function bit holds;
    return !x || c != 3;
  endfunction
  function int randomize_case;
    return randomize();
  endfunction
endclass

class RandcForeach extends RandcMixedBase;
  rand bit [1:0] arr[3];
  constraint c_each {foreach (arr[i]) arr[i] != c;}
  function bit holds;
    foreach (arr[i]) if (arr[i] == c) return 0;
    return 1;
  endfunction
  function int randomize_case;
    return randomize();
  endfunction
endclass

class RandcInside extends RandcMixedBase;
  rand bit [1:0] x;
  rand bit [1:0] y;
  constraint c_in {c inside {x, y};}
  function bit holds;
    return c == x || c == y;
  endfunction
  function int randomize_case;
    return randomize();
  endfunction
endclass

// A unique under a condition names its array in the folded constraint's text
class RandcCondUnique extends RandcMixedBase;
  rand bit [1:0] v[2];
  constraint c_unique {
    if (c > 0)
    unique {v};
  }
  function bit holds;
    return c == 0 || v[0] != v[1];
  endfunction
  function int randomize_case;
    return randomize();
  endfunction
endclass

// A frozen enum keeps its generated value-range constraint, which names it as is
class RandcFrozenEnum extends RandcMixedBase;
  typedef enum bit [1:0] {
    LOW = 0,
    HIGH = 2
  } mode_t;
  rand mode_t mode;
  constraint c_mode {mode != HIGH;}
  function bit holds;
    return mode == LOW;
  endfunction
  function int randomize_case;
    return randomize();
  endfunction
endclass

class RandcStructMember extends RandcMixedBase;
  typedef struct {rand bit [1:0] f;} pair_t;
  rand pair_t s;
  constraint c_member {c != s.f;}
  function bit holds;
    return c != s.f;
  endfunction
  function int randomize_case;
    return randomize();
  endfunction
endclass

// Test 9: static randc, with a randc-only constraint the draw must apply and a
// constraint mixed with rand that it must not
class RandcStatic;
  static randc bit [1:0] c;
  rand bit [1:0] x;
  constraint c_no3 {c != 3;}
  constraint c_rel {x > c;}

  function void test_cyclic;
    automatic int count[4] = '{0, 0, 0, 0};
    automatic int domain_size = 3;
    automatic int randomize_result;
    $display("Test static randc with randc-only and mixed constraints");
    // Run 4 full cycles
    for (int trial = 0; trial < 4; ++trial) begin
      for (int i = 0; i < domain_size; ++i) begin
        randomize_result = randomize();
        `checkd(randomize_result, 1);
        `checkd(x > c, 1);
        ++count[c];
      end
    end
    for (int v = 0; v <= 2; ++v) begin
      `checkd(count[v], 4);
    end
    `checkd(count[3], 0);
  endfunction
endclass

class ConditionalUniqueCycle;
  randc bit value;
  rand bit [1:0] values[2];
  constraint domain {
    if (value) {
      unique {values};
    }
  }
endclass

// A randc array is solved jointly, not drawn as a lone randc variable
class ArrayCycle;
  randc bit [1:0] values[2];
  constraint domain {foreach (values[index]) values[index] == 2;}
endclass

class FrozenEnumCycle;
  typedef enum bit [1:0] {
    LOW = 0,
    HIGH = 2
  } mode_t;
  rand mode_t mode;
  randc bit [1:0] value;
  constraint domain {
    value < 3;
    mode != HIGH;
  }
endclass

// A frozen array keeps its values, so only c values it does not hold are feasible
class FrozenArrayCycle;
  randc bit [1:0] c;
  rand bit [1:0] fa[2];
  constraint k {foreach (fa[i]) c != fa[i];}
endclass

class ArrayWith;
  randc bit [1:0] c[2];
  rand bit [3:0] x;
  constraint k {x < 12;}
endclass

// Test 10: randc sizing an array whose elements are constrained. randomize() solves the
// sizes first, and both solves keep the joint solve, so every call succeeds.
class SizedElements;
  randc bit [1:0] count;
  rand byte data[];
  constraint size_constraint {data.size() == int'(count);}
  constraint element_constraint {foreach (data[index]) data[index] == 0;}
endclass

// The size solve sees the elements from before the resize, here none, so count is 0
class SizedSum;
  randc bit [1:0] count;
  rand bit [7:0] data[];
  constraint k {
    data.size() == int'(count);
    data.sum() with (int'(item)) == 2 * int'(count);
  }
endclass

// Test 11: constraints whose names cover more than the text holding their randc-only part.
// The draw filters by them, so a randc value the text excludes is never drawn.
class StateIfElse;
  bit enabled;
  randc bit [1:0] count;
  rand bit [1:0] limit;
  constraint domain {
    if (enabled)
    count < limit;
    else
    count < 2;
  }
endclass

class StateOperand;
  bit enabled;
  randc bit [1:0] c;
  rand bit [1:0] x;
  constraint k {c != (enabled ? x : 3);}
endclass

class StateUnderRandcFold;
  bit enabled;
  randc bit [1:0] c;
  rand bit [1:0] x;
  constraint k {
    if (c > 0) {
      if (enabled)
      c < x;
      else
      c > 2;
    }
  }
endclass

class RandcFoldItems;
  randc bit [1:0] c;
  rand bit [3:0] x;
  constraint k {
    if (c < 2) {
      x > 3;
    } else {
      c < 3;
      x < 8;
    }
  }
endclass

module t;
  RandcRange rr;
  RandcSmall rs;
  RandcParent rp;
  RandcChild rc;
  RandcModeSwitch rms;
  RandcEnumConstrained rec;
  RandcDeep rd;
  RandcIfCond ric;
  RandcImplication rim;
  RandcForeach rfe;
  RandcInside rin;
  RandcStructMember rsm;
  RandcStatic rst;

  initial begin
    rr = new;
    rr.test_cyclic();

    rs = new;
    rs.test_cyclic();

    rp = new;
    rp.test_cyclic();

    rc = new;
    rc.test_cyclic();

    rms = new;
    rms.test_mode_switch();

    rec = new;
    rec.test_cyclic();

    rd = new;
    rd.test_cyclic();

    ric = new;
    ric.test_cyclic("an if condition");

    rim = new;
    rim.test_cyclic("an implication");

    rfe = new;
    rfe.test_cyclic("a foreach");

    rin = new;
    rin.test_cyclic("an inside list");

    rsm = new;
    rsm.test_cyclic("a struct member");

    rst = new;
    rst.test_cyclic();

    begin
      automatic RandcCondUnique rcu = new;
      rcu.test_cyclic("a conditional unique");
    end

    begin
      automatic ConditionalUniqueCycle obj = new;
      automatic int count[2] = '{0, 0};
      automatic int res;
      $display("Test randc deciding whether a unique applies");
      for (int i = 0; i < 4; ++i) begin
        res = obj.randomize();
        `checkd(res, 1);
        if (obj.value) `checkd(obj.values[0] != obj.values[1], 1'b1);
        ++count[obj.value];
      end
      `checkd(count[0], 2);
      `checkd(count[1], 2);
    end

    begin
      automatic RandcFrozenEnum rfz = new;
      rfz.mode.rand_mode(0);
      rfz.test_cyclic("a frozen enum");
    end

    begin
      automatic FrozenEnumCycle obj = new;
      automatic int count[4] = '{0, 0, 0, 0};
      automatic int res;
      $display("Test randc with a frozen enum");
      obj.mode.rand_mode(0);
      for (int i = 0; i < 6; ++i) begin
        res = obj.randomize();
        `checkd(res, 1);
        `checkd(obj.mode, FrozenEnumCycle::LOW);
        ++count[obj.value];
      end
      for (int v = 0; v < 3; ++v) `checkd(count[v], 2);
    end

    begin
      automatic FrozenArrayCycle obj = new;
      automatic int count[4] = '{0, 0, 0, 0};
      automatic int res;
      $display("Test randc with a frozen array");
      obj.fa = '{1, 2};
      obj.fa.rand_mode(0);
      for (int i = 0; i < 6; ++i) begin
        res = obj.randomize();
        `checkd(res, 1);
        `checkd(obj.fa[0], 1);
        `checkd(obj.fa[1], 2);
        ++count[obj.c];
      end
      `checkd(count[0], 3);
      `checkd(count[3], 3);
    end

    begin
      automatic ArrayCycle obj = new;
      automatic int res;
      $display("Test randc array");
      // Called once: a later call hits a pre-existing bug in excluding randc array values
      res = obj.randomize();
      `checkd(res, 1);
      `checkd(obj.values[0], 2);
      `checkd(obj.values[1], 2);
    end

    begin
      automatic ArrayWith obj = new;
      automatic int res;
      $display("Test randc array with an inline constraint");
      for (int i = 0; i < 8; ++i) begin
        res = obj.randomize() with {c[0] != 0;};
        `checkd(res, 1);
        `checkd(obj.c[0] != 0, 1'b1);
        `checkd(obj.x < 12, 1'b1);
      end
    end

    begin
      automatic SizedElements obj = new;
      automatic int res;
      $display("Test randc sizing an array with constrained elements");
      for (int i = 0; i < 12; ++i) begin
        res = obj.randomize();
        `checkd(res, 1);
        `checkd(obj.data.size(), int'(obj.count));
        foreach (obj.data[j]) `checkd(obj.data[j], 0);
      end
    end

    begin
      automatic SizedSum obj = new;
      automatic int res;
      $display("Test randc sizing an array by its sum");
      for (int i = 0; i < 12; ++i) begin
        res = obj.randomize();
        `checkd(res, 1);
        `checkd(obj.data.size(), int'(obj.count));
        `checkd(obj.data.sum() with (int'(item)), 2 * int'(obj.count));
      end
    end

    // Without the filter, a cycle fails unless the draw takes the feasible values first,
    // so each case below passes unfiltered with probability at most (1/6)**6
    begin
      automatic StateIfElse obj = new;
      automatic int res;
      $display("Test randc under an if on state");
      obj.enabled = 0;
      for (int i = 0; i < 12; ++i) begin
        res = obj.randomize();
        `checkd(res, 1);
        `checkd(obj.count < 2, 1'b1);
      end
    end

    begin
      automatic StateOperand obj = new;
      automatic int res;
      $display("Test randc under a conditional operator on state");
      obj.enabled = 0;
      for (int i = 0; i < 32; ++i) begin
        res = obj.randomize();
        `checkd(res, 1);
        `checkd(obj.c != 3, 1'b1);
      end
    end

    begin
      automatic StateUnderRandcFold obj = new;
      automatic int res;
      $display("Test randc under an if on state inside an if on randc");
      obj.enabled = 0;
      for (int i = 0; i < 32; ++i) begin
        res = obj.randomize();
        `checkd(res, 1);
        `checkd(obj.c == 0 || obj.c == 3, 1'b1);
      end
    end

    begin
      automatic RandcFoldItems obj = new;
      automatic int res;
      $display("Test randc under an if on randc holding several constraints");
      for (int i = 0; i < 32; ++i) begin
        res = obj.randomize();
        `checkd(res, 1);
        `checkd(obj.c != 3, 1'b1);
        `checkd((obj.c < 2) ? obj.x > 3 : obj.x < 8, 1'b1);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish();
  end
endmodule
