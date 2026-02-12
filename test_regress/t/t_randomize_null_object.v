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

// Test randomize() on null object handle.
// Per IEEE 1800 Section 18.4, randomize() on null should return 0.

class SimpleRandClass;
  rand bit [7:0] value;

  constraint value_con {
    value > 0 && value < 200;
  }

  function new();
  endfunction
endclass

module t;
  SimpleRandClass obj;
  int rand_result;

  initial begin
    // obj is null (not constructed)
    obj = null;

    // Per IEEE 1800, calling randomize() on null should return 0
    rand_result = obj.randomize();
    `checkd(rand_result, 0);

    // Now test with a valid object
    obj = new();
    rand_result = obj.randomize();
    `checkd(rand_result, 1);
    `check_range(obj.value, 1, 199);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
