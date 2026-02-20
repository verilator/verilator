// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test: rand_mode on nested object's variable should not cause Z3 solver error.
// Previously, the generated SMT constraint used "#x0" instead of the variable
// name for nested rand variables when rand_mode was involved, causing a width
// mismatch in the constraint solver.

class InnerClass;
  rand bit [7:0] inner_val1;
  rand bit [7:0] inner_val2;

  constraint inner_con {
    inner_val1 inside {[8'd10 : 8'd50]};
    inner_val2 inside {[8'd100 : 8'd200]};
  }

  function new();
    inner_val1 = 0;
    inner_val2 = 0;
  endfunction
endclass

class OuterClass;
  rand InnerClass nested_obj;
  rand bit [7:0] outer_val;

  constraint outer_con {outer_val inside {[8'd1 : 8'd20]};}

  function new();
    nested_obj = new();
    outer_val = 0;
  endfunction
endclass

module t_constraint_global_nested_randmode;
  OuterClass obj;
  int rand_ok;
  int change_count;
  bit [7:0] prev_val;

  initial begin
    obj = new();

    // Test 1: Normal randomization of nested object with constraints
    rand_ok = obj.randomize();
    if (rand_ok == 0) $stop;
    if (obj.nested_obj.inner_val1 < 8'd10 || obj.nested_obj.inner_val1 > 8'd50) $stop;
    if (obj.nested_obj.inner_val2 < 8'd100 || obj.nested_obj.inner_val2 > 8'd200) $stop;
    if (obj.outer_val < 8'd1 || obj.outer_val > 8'd20) $stop;

    // Test 2: Multiple randomizations with constraint checking
    change_count = 0;
    prev_val = obj.nested_obj.inner_val1;
    repeat (10) begin
      rand_ok = obj.randomize();
      if (rand_ok == 0) $stop;
      if (obj.nested_obj.inner_val1 < 8'd10 || obj.nested_obj.inner_val1 > 8'd50) $stop;
      if (obj.nested_obj.inner_val2 < 8'd100 || obj.nested_obj.inner_val2 > 8'd200) $stop;
      if (obj.outer_val < 8'd1 || obj.outer_val > 8'd20) $stop;
      if (obj.nested_obj.inner_val1 != prev_val) change_count++;
      prev_val = obj.nested_obj.inner_val1;
    end
    if (change_count == 0) $stop;

    // Test 3: rand_mode(0) on nested var - must not crash solver
    void'(obj.nested_obj.inner_val1.rand_mode(0));
    if (obj.nested_obj.inner_val1.rand_mode() != 0) $stop;
    // Calling randomize must not cause a solver crash
    rand_ok = obj.randomize();
    // (randomize may return 0 due to constraint interaction - separate issue)

    // Test 4: Re-enable rand_mode and verify randomization resumes
    void'(obj.nested_obj.inner_val1.rand_mode(1));
    if (obj.nested_obj.inner_val1.rand_mode() != 1) $stop;
    change_count = 0;
    prev_val = obj.nested_obj.inner_val1;
    repeat (10) begin
      rand_ok = obj.randomize();
      if (rand_ok == 0) $stop;
      if (obj.nested_obj.inner_val1 != prev_val) change_count++;
      prev_val = obj.nested_obj.inner_val1;
    end
    if (change_count == 0) $stop;

    // Test 5: rand_mode(0) on entire nested object - must not crash solver
    void'(obj.nested_obj.rand_mode(0));
    rand_ok = obj.randomize();
    // (randomize may return 0 due to constraint interaction - separate issue)

    // Test 6: Re-enable nested object and verify randomization resumes
    void'(obj.nested_obj.rand_mode(1));
    change_count = 0;
    prev_val = obj.nested_obj.inner_val1;
    repeat (10) begin
      rand_ok = obj.randomize();
      if (rand_ok == 0) $stop;
      if (obj.nested_obj.inner_val1 != prev_val) change_count++;
      prev_val = obj.nested_obj.inner_val1;
    end
    if (change_count == 0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
