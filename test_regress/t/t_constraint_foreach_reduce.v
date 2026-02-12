// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test array reduction methods (sum, or, xor) with 'with' clause inside
// constraints, combined with foreach and implication.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d-%0d\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);
// verilog_format: on

// foreach + implication + sum with
class ImplySumTest;
  rand bit enable [4];
  rand int values [4];

  constraint imply_con {
    foreach (values[i]) {
      enable[i] -> (values[i] >= 100 && values[i] <= 200);
    }
  }

  constraint min_enabled {
    enable.sum() with (int'(item)) >= 2;
  }

  function new();
  endfunction
endclass

// sum with exact count
class ExactSumTest;
  rand bit flags [8];

  constraint exact_four {
    flags.sum() with (int'(item)) == 4;
  }

  function new();
  endfunction
endclass

// or reduction in constraint
class OrReduceTest;
  rand bit lanes [4];

  constraint at_least_one {
    lanes.or() with (int'(item)) == 1;
  }

  function new();
  endfunction
endclass

module t;
  initial begin
    automatic ImplySumTest is_obj = new;
    automatic ExactSumTest es_obj = new;
    automatic OrReduceTest or_obj = new;
    int sum_val;

    // Test 1: foreach + implication + sum with
    repeat (10) begin
      `checkd(is_obj.randomize(), 1)
      sum_val = 0;
      foreach (is_obj.enable[i]) sum_val += int'(is_obj.enable[i]);
      `check_range(sum_val, 2, 4)
      foreach (is_obj.values[i]) begin
        if (is_obj.enable[i]) begin
          `check_range(is_obj.values[i], 100, 200)
        end
      end
    end

    // Test 2: sum with exact count
    repeat (10) begin
      `checkd(es_obj.randomize(), 1)
      sum_val = 0;
      foreach (es_obj.flags[i]) sum_val += int'(es_obj.flags[i]);
      `checkd(sum_val, 4)
    end

    // Test 3: or reduction
    repeat (10) begin
      `checkd(or_obj.randomize(), 1)
      sum_val = 0;
      foreach (or_obj.lanes[i]) sum_val |= int'(or_obj.lanes[i]);
      `checkd(sum_val, 1)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
