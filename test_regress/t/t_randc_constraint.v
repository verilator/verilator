// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test: randc variables with additional constraints limiting values
// IEEE 1800 Section 18.4.2: randc cyclic behavior over constrained domain

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
        if (randomize_result !== 1) begin
          $display("%%Error: randomize() failed");
          $stop;
        end
        if (value < 3 || value > 10) begin
          $display("%%Error: value %0d out of constrained range [3:10]", value);
          $stop;
        end
`ifdef TEST_VERBOSE
        $display("  trial=%0d i=%0d value=%0d", trial, i, value);
`endif
        ++count[value];
      end
    end
    // After 3 full cycles, each value in [3,10] should appear exactly 3 times
    for (int v = 3; v <= 10; ++v) begin
      if (count[v] != 3) begin
        $display("%%Error: value %0d appeared %0d times, expected 3", v, count[v]);
        $stop;
      end
    end
    // Values outside [3,10] should never appear
    for (int v = 0; v < 3; ++v) begin
      if (count[v] != 0) begin
        $display("%%Error: value %0d appeared %0d times, expected 0", v, count[v]);
        $stop;
      end
    end
    for (int v = 11; v < 16; ++v) begin
      if (count[v] != 0) begin
        $display("%%Error: value %0d appeared %0d times, expected 0", v, count[v]);
        $stop;
      end
    end
  endfunction
endclass

class RandcSmall;
  randc bit [1:0] val;  // 4 possible values: 0,1,2,3
  constraint c_exclude { val != 0; }  // 3 valid values: 1,2,3

  function void test_cyclic;
    automatic int count[4];
    automatic int domain_size = 3;
    automatic int randomize_result;
    $display("Test randc with exclude constraint (val != 0)");
    // Run 4 full cycles
    for (int trial = 0; trial < 4; ++trial) begin
      for (int i = 0; i < domain_size; ++i) begin
        randomize_result = randomize();
        if (randomize_result !== 1) begin
          $display("%%Error: randomize() failed");
          $stop;
        end
        if (val == 0) begin
          $display("%%Error: val == 0 violates constraint");
          $stop;
        end
`ifdef TEST_VERBOSE
        $display("  trial=%0d i=%0d val=%0d", trial, i, val);
`endif
        ++count[val];
      end
    end
    // After 4 full cycles, each of 1,2,3 should appear exactly 4 times
    if (count[0] != 0) begin
      $display("%%Error: val 0 appeared %0d times, expected 0", count[0]);
      $stop;
    end
    for (int v = 1; v <= 3; ++v) begin
      if (count[v] != 4) begin
        $display("%%Error: val %0d appeared %0d times, expected 4", v, count[v]);
        $stop;
      end
    end
  endfunction
endclass

// Test 3: Inheritance - parent randc with constraint, child inherits
class RandcParent;
  randc bit [2:0] code;  // 8 values: 0-7
  constraint c_positive { code > 0; }  // 7 valid values: 1-7

  function void test_cyclic;
    automatic int count[8];
    automatic int domain_size = 7;
    automatic int randomize_result;
    $display("Test randc parent with constraint (code > 0)");
    for (int trial = 0; trial < 3; ++trial) begin
      for (int i = 0; i < domain_size; ++i) begin
        randomize_result = randomize();
        if (randomize_result !== 1) begin
          $display("%%Error: randomize() failed");
          $stop;
        end
        if (code == 0) begin
          $display("%%Error: code == 0 violates constraint");
          $stop;
        end
`ifdef TEST_VERBOSE
        $display("  trial=%0d i=%0d code=%0d", trial, i, code);
`endif
        ++count[code];
      end
    end
    for (int v = 1; v <= 7; ++v) begin
      if (count[v] != 3) begin
        $display("%%Error: code %0d appeared %0d times, expected 3", v, count[v]);
        $stop;
      end
    end
    if (count[0] != 0) begin
      $display("%%Error: code 0 appeared %0d times, expected 0", count[0]);
      $stop;
    end
  endfunction
endclass

class RandcChild extends RandcParent;
  // Inherits randc code and c_positive constraint
  constraint c_upper { code <= 5; }  // Further restrict: 1-5 (5 values)

  function void test_cyclic;
    automatic int count[8];
    automatic int domain_size = 5;
    automatic int randomize_result;
    $display("Test randc child with inherited + additional constraint (1 <= code <= 5)");
    for (int trial = 0; trial < 4; ++trial) begin
      for (int i = 0; i < domain_size; ++i) begin
        randomize_result = randomize();
        if (randomize_result !== 1) begin
          $display("%%Error: randomize() failed");
          $stop;
        end
        if (code == 0 || code > 5) begin
          $display("%%Error: code %0d out of range [1:5]", code);
          $stop;
        end
`ifdef TEST_VERBOSE
        $display("  trial=%0d i=%0d code=%0d", trial, i, code);
`endif
        ++count[code];
      end
    end
    for (int v = 1; v <= 5; ++v) begin
      if (count[v] != 4) begin
        $display("%%Error: code %0d appeared %0d times, expected 4", v, count[v]);
        $stop;
      end
    end
    for (int v = 6; v <= 7; ++v) begin
      if (count[v] != 0) begin
        $display("%%Error: code %0d appeared %0d times, expected 0", v, count[v]);
        $stop;
      end
    end
  endfunction
endclass

// Test 4: constraint_mode() interaction
// Verifies randc cyclic behavior adapts when constraints are toggled at runtime.
// Note: randc cycles are continuous, not per-phase, so we verify constraint
// enforcement and that all valid values eventually appear rather than exact counts.
class RandcModeSwitch;
  randc bit [1:0] x;  // 4 values: 0-3
  constraint c_nonzero { x != 0; }  // 3 valid values: 1,2,3

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
        if (randomize_result !== 1) begin
          $display("%%Error: phase1 randomize() failed");
          $stop;
        end
        if (x == 0) begin
          $display("%%Error: phase1 x == 0 violates active constraint");
          $stop;
        end
`ifdef TEST_VERBOSE
        $display("  phase1 i=%0d x=%0d", i, x);
`endif
        seen[x] = 1;
      end
      for (int v = 1; v <= 3; ++v) begin
        if (!seen[v]) begin
          $display("%%Error: phase1 value %0d never seen in 6 calls", v);
          $stop;
        end
      end
    end

    // Phase 2: constraint OFF -> x=0 should eventually appear
    $display("Test constraint_mode: phase 2 (constraint OFF)");
    c_nonzero.constraint_mode(0);
    seen_zero = 0;
    // Run enough calls (2 full cycles of 4 + margin) to see all values
    for (int i = 0; i < 12; ++i) begin
      randomize_result = randomize();
      if (randomize_result !== 1) begin
        $display("%%Error: phase2 randomize() failed");
        $stop;
      end
`ifdef TEST_VERBOSE
      $display("  phase2 i=%0d x=%0d", i, x);
`endif
      if (x == 0) seen_zero = 1;
    end
    if (!seen_zero) begin
      $display("%%Error: phase2 x=0 never appeared with constraint OFF");
      $stop;
    end

    // Phase 3: constraint back ON -> x should never be 0 again
    $display("Test constraint_mode: phase 3 (constraint ON again)");
    c_nonzero.constraint_mode(1);
    for (int i = 0; i < 9; ++i) begin
      randomize_result = randomize();
      if (randomize_result !== 1) begin
        $display("%%Error: phase3 randomize() failed");
        $stop;
      end
      if (x == 0) begin
        $display("%%Error: phase3 x == 0 violates re-enabled constraint");
        $stop;
      end
`ifdef TEST_VERBOSE
      $display("  phase3 i=%0d x=%0d", i, x);
`endif
    end
  endfunction
endclass

// Test 5: Enum randc with constraint excluding some values
// Use a 2-bit enum where all bit values are valid enum members,
// so the solver domain matches the enum domain exactly.
class RandcEnumConstrained;
  typedef enum bit [1:0] {
    RED   = 0,
    GREEN = 1,
    BLUE  = 2,
    WHITE = 3
  } color_t;

  randc color_t color;
  constraint c_no_white { color != WHITE; }  // 3 valid: RED, GREEN, BLUE

  function void test_cyclic;
    automatic int count[4] = '{0, 0, 0, 0};
    automatic int domain_size = 3;
    automatic int randomize_result;
    $display("Test randc enum with constraint (exclude WHITE)");
    for (int trial = 0; trial < 4; ++trial) begin
      for (int i = 0; i < domain_size; ++i) begin
        randomize_result = randomize();
        if (randomize_result !== 1) begin
          $display("%%Error: randomize() failed");
          $stop;
        end
        if (color == WHITE) begin
          $display("%%Error: color == WHITE violates constraint");
          $stop;
        end
`ifdef TEST_VERBOSE
        $display("  trial=%0d i=%0d color=%0d", trial, i, color);
`endif
        ++count[color];
      end
    end
    for (int v = 0; v <= 2; ++v) begin
      if (count[v] != 4) begin
        $display("%%Error: color %0d appeared %0d times, expected 4", v, count[v]);
        $stop;
      end
    end
    if (count[3] != 0) begin
      $display("%%Error: WHITE appeared %0d times, expected 0", count[3]);
      $stop;
    end
  endfunction
endclass

module t;
  RandcRange rr;
  RandcSmall rs;
  RandcParent rp;
  RandcChild rc;
  RandcModeSwitch rms;
  RandcEnumConstrained rec;

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

    $write("*-* All Finished *-*\n");
    $finish();
  end
endmodule
