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

// Test: 'this' keyword inside inline randomize() with {} constraint blocks.
// 'this' should refer to the object being randomized (IEEE 1800-2023 18.7).

class DataItem;
  rand bit [7:0] value;
  rand bit [7:0] limit;
  constraint default_con {limit inside {[8'd50 : 8'd200]};}
endclass

// Test 4: 'this' in inline constraint called from another class method.
// 'this' must bind to the randomized object, not the calling class.
class Caller;
  rand bit [7:0] own_value;
  function int do_rand(DataItem item);
    return item.randomize() with {
      this.value > 8'd30;
      this.value < 8'd40;
    };
  endfunction
endclass

module t;
  initial begin
    automatic DataItem item = new();
    automatic Caller caller = new();
    automatic int rand_ok;

    // Test 1: 'this.member' in inline constraint from module-level code
    rand_ok = item.randomize() with {
      this.value > 8'd10;
      this.value < 8'd50;
    };
    `checkd(rand_ok, 1)
    `check_range(item.value, 11, 49)
    `check_range(item.limit, 50, 200)

    // Test 2: multiple 'this.member' references
    rand_ok = item.randomize() with {
      this.value > 8'd20;
      this.value < 8'd30;
    };
    `checkd(rand_ok, 1)
    `check_range(item.value, 21, 29)

    // Test 3: mix of 'this.member' and unqualified member
    rand_ok = item.randomize() with {
      this.value > 8'd5;
      this.value < 8'd100;
      limit > 8'd150;
    };
    `checkd(rand_ok, 1)
    `check_range(item.value, 6, 99)
    `check_range(item.limit, 151, 200)

    // Test 4: 'this' binds to randomized object, not calling class
    rand_ok = caller.do_rand(item);
    `checkd(rand_ok, 1)
    `check_range(item.value, 31, 39)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
