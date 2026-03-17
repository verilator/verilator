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

// Test: rand_mode(0) on nested sub-object members must prevent solver
// from overwriting the variable. Previously, write_var registered the
// variable unconditionally, so the solver wrote it back even when
// rand_mode was off.

class InnerClass;
  rand bit [7:0] val1;
  rand bit [7:0] val2;
  rand bit [7:0] val3;
  constraint inner_c {
    val1 inside {[8'd10 : 8'd50]};
    val2 inside {[8'd60 : 8'd100]};
    val3 inside {[8'd110 : 8'd150]};
  }
  function new();
    val1 = 0;
    val2 = 0;
    val3 = 0;
  endfunction
endclass

class OuterClass;
  rand InnerClass nested;
  rand bit [7:0] outer_val;
  constraint outer_c { outer_val inside {[8'd1 : 8'd20]}; }
  function new();
    nested = new();
    outer_val = 0;
  endfunction
endclass

module t;
  initial begin
    OuterClass obj;
    obj = new;

    // Test 1: Normal randomize
    repeat (20) begin
      `checkd(obj.randomize(), 1)
      `check_range(obj.nested.val1, 8'd10, 8'd50)
      `check_range(obj.nested.val2, 8'd60, 8'd100)
      `check_range(obj.nested.val3, 8'd110, 8'd150)
      `check_range(obj.outer_val, 8'd1, 8'd20)
    end

    // Test 2: rand_mode(0) on val1 -- must hold assigned value
    void'(obj.nested.val1.rand_mode(0));
    obj.nested.val1 = 8'd42;
    repeat (20) begin
      `checkd(obj.randomize(), 1)
      `checkd(obj.nested.val1, 8'd42)
      `check_range(obj.nested.val2, 8'd60, 8'd100)
      `check_range(obj.nested.val3, 8'd110, 8'd150)
    end

    // Test 3: rand_mode(0) on val2 as well
    void'(obj.nested.val2.rand_mode(0));
    obj.nested.val2 = 8'd77;
    repeat (20) begin
      `checkd(obj.randomize(), 1)
      `checkd(obj.nested.val1, 8'd42)
      `checkd(obj.nested.val2, 8'd77)
      `check_range(obj.nested.val3, 8'd110, 8'd150)
    end

    // Test 4: Re-enable both and verify randomization resumes
    void'(obj.nested.val1.rand_mode(1));
    void'(obj.nested.val2.rand_mode(1));
    repeat (20) begin
      `checkd(obj.randomize(), 1)
      `check_range(obj.nested.val1, 8'd10, 8'd50)
      `check_range(obj.nested.val2, 8'd60, 8'd100)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
