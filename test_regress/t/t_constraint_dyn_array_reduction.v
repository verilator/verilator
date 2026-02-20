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
// Fixed-size arrays expand reductions at compile time, but dynamic arrays
// remain as AstCMethodHard nodes that need constraint solver support.

module t;

  class DynReductionTest;
    rand bit [7:0] data [];
    rand bit [7:0] xor_result;
    rand bit [7:0] sum_result;
    rand bit [7:0] and_result;
    rand bit [7:0] or_result;
    rand bit [7:0] prod_result;

    function new();
      data = new[4];
    endfunction

    constraint c_size { data.size() == 4; }
    constraint c_xor { xor_result == data.xor(); }
    constraint c_sum { sum_result == data.sum(); }
    constraint c_and { and_result == data.and(); }
    constraint c_or { or_result == data.or(); }
    constraint c_prod { prod_result == data.product(); }
  endclass

  initial begin
    static DynReductionTest t = new();
    repeat (3) begin
      `checkd(t.randomize(), 1)
      // Verify each reduction against computed value
      begin
        bit [7:0] exp_xor = 0;
        bit [7:0] exp_sum = 0;
        bit [7:0] exp_and = 8'hff;
        bit [7:0] exp_or = 0;
        bit [7:0] exp_prod = 8'd1;
        foreach (t.data[i]) begin
          exp_xor ^= t.data[i];
          exp_sum += t.data[i];
          exp_and &= t.data[i];
          exp_or |= t.data[i];
          exp_prod *= t.data[i];
        end
        `checkh(t.xor_result, exp_xor)
        `checkh(t.sum_result, exp_sum)
        `checkh(t.and_result, exp_and)
        `checkh(t.or_result, exp_or)
        `checkh(t.prod_result, exp_prod)
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
