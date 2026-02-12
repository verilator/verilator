// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test: unique constraint on explicit array element subset
// IEEE 1800-2017 Section 18.5.9
//
// Uses bit [3:0] (16 possible values) with 5-element unique subsets
// so that without proper constraint enforcement, collisions are
// virtually guaranteed across 20 iterations.

class UniqueElemSubset;
  rand bit [3:0] arr[10];

  // Unique applied to a subset of array indices
  constraint unique_subset_con {
    unique { arr[2], arr[3], arr[4], arr[5], arr[6] };
  }

  function new();
  endfunction

  function bit check_unique();
    for (int i = 2; i <= 6; i++)
      for (int j = i + 1; j <= 6; j++)
        if (arr[i] == arr[j]) return 0;
    return 1;
  endfunction
endclass

class UniqueElemFour;
  rand bit [3:0] data[8];

  // Unique on 4 explicit elements
  constraint unique_data_con {
    unique { data[1], data[2], data[3], data[4] };
  }

  function new();
  endfunction

  function bit check_unique();
    for (int i = 1; i <= 4; i++)
      for (int j = i + 1; j <= 4; j++)
        if (data[i] == data[j]) return 0;
    return 1;
  endfunction
endclass

module t;
  UniqueElemSubset ues;
  UniqueElemFour uef;

  initial begin
    // Test 1: unique on 5 explicit array elements
    ues = new();
    repeat (20) begin
      `checkd(ues.randomize(), 1)
      `checkd(ues.check_unique(), 1)
    end

    // Test 2: unique on 4 explicit array elements
    uef = new();
    repeat (20) begin
      `checkd(uef.randomize(), 1)
      `checkd(uef.check_unique(), 1)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
