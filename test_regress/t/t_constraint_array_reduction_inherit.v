// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Wilson Snyder and Contributors
// SPDX-License-Identifier: CC0-1.0

// Test array reduction methods in constraints with class inheritance (issue #7226)
// The bug was that .sum() in a constraint crashed with "Can't locate varref scope"
// when the class extends another class.
// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Base;
  rand int base_val;
  constraint c_base {base_val inside {[1:100]};}
endclass

// Derived class with dynamic array and .sum() constraint -- the crash scenario
class Derived extends Base;
  rand int arr[];
  constraint c_size {arr.size() == 4;}
  constraint c_sum {arr.sum() == 200;}
  function new();
    arr = new[4];
  endfunction
endclass

// Multi-level inheritance: ensure deeper hierarchies also work
class GrandChild extends Derived;
  rand bit [7:0] extra[3];
  constraint c_extra_or {extra.or() != 0;}
endclass

module t;

  initial begin
    static Derived d = new();
    static GrandChild g = new();
    int sum_check;

    // Test single-level inheritance with .sum()
    repeat (5) begin
      `checkd(d.randomize(), 1)
      `checkd(d.arr.size(), 4)
      sum_check = 0;
      foreach (d.arr[i]) sum_check += d.arr[i];
      `checkd(sum_check, 200)
      `checkd(d.base_val inside {[1:100]}, 1)
    end

    // Test multi-level inheritance with reduction on fixed array
    repeat (5) begin
      bit [7:0] or_check;
      `checkd(g.randomize(), 1)
      `checkd(g.arr.size(), 4)
      sum_check = 0;
      foreach (g.arr[i]) sum_check += g.arr[i];
      `checkd(sum_check, 200)
      or_check = 0;
      foreach (g.extra[i]) or_check |= g.extra[i];
      if (or_check == 0) begin
        $write("%%Error: %s:%0d: extra.or() should be nonzero\n", `__FILE__, `__LINE__);
        `stop;
      end
      `checkd(g.base_val inside {[1:100]}, 1)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
