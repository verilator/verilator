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

// Test that rand variables used as array indices in constraints are treated
// as symbolic in the solver, not evaluated at C++ constraint setup time.

class RandArrayIndexTest;
  rand bit [1:0] idx;
  rand bit [7:0] data [4];
  rand bit [7:0] selected_value;

  constraint solve_order { solve idx before selected_value; }
  constraint value_match { selected_value == data[idx]; }
  constraint data_values {
    foreach (data[i]) {
      data[i] inside {[8'd10:8'd50]};
    }
  }
endclass

module t;
  initial begin
    static RandArrayIndexTest obj = new();
    repeat (20) begin
      `checkd(obj.randomize(), 1)
      `checkd(obj.selected_value, obj.data[obj.idx])
      `check_range(obj.selected_value, 8'd10, 8'd50)
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
