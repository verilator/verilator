// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test dynamic array reduction methods (xor, sum, and, or, product)
// without 'with' clause in constraints.
// Each method is tested in a separate class to avoid conflicting constraints.

module t;

  class XorTest;
    rand bit [7:0] data[];
    rand bit [7:0] result;
    function new();
      data = new[4];
    endfunction
    constraint c_size {data.size() == 4;}
    constraint c_xor {result == data.xor();}
  endclass

  class SumTest;
    rand bit [7:0] data[];
    rand bit [7:0] result;
    function new();
      data = new[4];
    endfunction
    constraint c_size {data.size() == 4;}
    constraint c_sum {result == data.sum();}
  endclass

  class AndTest;
    rand bit [7:0] data[];
    rand bit [7:0] result;
    function new();
      data = new[4];
    endfunction
    constraint c_size {data.size() == 4;}
    constraint c_and {result == data.and();}
  endclass

  class OrTest;
    rand bit [7:0] data[];
    rand bit [7:0] result;
    function new();
      data = new[4];
    endfunction
    constraint c_size {data.size() == 4;}
    constraint c_or {result == data.or();}
  endclass

  class ProductTest;
    rand bit [7:0] data[];
    rand bit [7:0] result;
    function new();
      data = new[4];
    endfunction
    constraint c_size {data.size() == 4;}
    constraint c_prod {result == data.product();}
  endclass

  initial begin
    static XorTest t_xor = new();
    static SumTest t_sum = new();
    static AndTest t_and = new();
    static OrTest t_or = new();
    static ProductTest t_prod = new();

    repeat (10) begin
      bit [7:0] exp;
      int i;

      // Test xor
      `checkd(t_xor.randomize(), 1)
      exp = 0;
      foreach (t_xor.data[i]) exp ^= t_xor.data[i];
      `checkh(t_xor.result, exp)

      // Test sum
      `checkd(t_sum.randomize(), 1)
      exp = 0;
      foreach (t_sum.data[i]) exp += t_sum.data[i];
      `checkh(t_sum.result, exp)

      // Test and
      `checkd(t_and.randomize(), 1)
      exp = 8'hff;
      foreach (t_and.data[i]) exp &= t_and.data[i];
      `checkh(t_and.result, exp)

      // Test or
      `checkd(t_or.randomize(), 1)
      exp = 0;
      foreach (t_or.data[i]) exp |= t_or.data[i];
      `checkh(t_or.result, exp)

      // Test product
      `checkd(t_prod.randomize(), 1)
      exp = 8'd1;
      foreach (t_prod.data[i]) exp *= t_prod.data[i];
      `checkh(t_prod.result, exp)
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
