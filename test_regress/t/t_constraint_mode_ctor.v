// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test constraint_mode() called inside class constructor (function new)

class ConstraintModeInCtor;
  rand bit [7:0] value;

  constraint low_range_c {value < 50;}
  constraint high_range_c {
    value >= 50;
    value < 200;
  }

  function new;
    // Disable high_range_c in constructor - only low_range_c should be active
    high_range_c.constraint_mode(0);
  endfunction
endclass

module t;
  initial begin
    automatic ConstraintModeInCtor obj = new;
    automatic int i;

    // Test 1: constraint_mode(0) in constructor should disable constraint
    for (i = 0; i < 20; i++) begin
      void'(obj.randomize());
      if (obj.value >= 50) $stop;
    end

    // Test 2: Query constraint_mode state set in constructor
    if (obj.low_range_c.constraint_mode != 1) $stop;
    if (obj.high_range_c.constraint_mode != 0) $stop;

    // Test 3: Switch constraints at runtime
    obj.low_range_c.constraint_mode(0);
    obj.high_range_c.constraint_mode(1);
    for (i = 0; i < 20; i++) begin
      void'(obj.randomize());
      if (obj.value < 50 || obj.value >= 200) $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
