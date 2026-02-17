// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test unique constraint on explicit array element subsets (IEEE 18.5.9).
// bit [3:0] keeps the value space small so collisions are near-certain
// without proper constraint enforcement.

class UniqueElemSubset;
  rand bit [3:0] arr[10];

  constraint unique_subset_con {unique {arr[2], arr[3], arr[4], arr[5], arr[6]};}

  function new();
  endfunction

  function bit check_unique();
    for (int i = 2; i <= 6; i++) begin
      for (int j = i + 1; j <= 6; j++) begin
        if (arr[i] == arr[j]) return 0;
      end
    end
    return 1;
  endfunction
endclass

class UniqueElemFour;
  rand bit [3:0] data[8];

  constraint unique_data_con {unique {data[1], data[2], data[3], data[4]};}

  function new();
  endfunction

  function bit check_unique();
    for (int i = 1; i <= 4; i++) begin
      for (int j = i + 1; j <= 4; j++) begin
        if (data[i] == data[j]) return 0;
      end
    end
    return 1;
  endfunction
endclass

class UniqueElemSingle;
  rand bit [3:0] val[4];

  constraint unique_single_con {unique {val[0]};}

  function new();
  endfunction
endclass

module t;
  UniqueElemSubset ues;
  UniqueElemFour uef;
  UniqueElemSingle uesgl;

  initial begin
    ues = new();
    repeat (20) begin
      `checkd(ues.randomize(), 1)
      `checkd(ues.check_unique(), 1)
    end

    uef = new();
    repeat (20) begin
      `checkd(uef.randomize(), 1)
      `checkd(uef.check_unique(), 1)
    end

    uesgl = new();
    repeat (5) begin
      `checkd(uesgl.randomize(), 1)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
