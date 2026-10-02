// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Limits of the bins of 'with' filters, which are found when the covergroup is constructed

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit [32:0] v33;
  bit [7:0] v8;

  // Each is evaluated for at most 2**32 candidates, which bounds known when constructed give
  covergroup cg_candidates(bit [32:0] high, bit [32:0] low);
    all: coverpoint v33 {
      bins b = {[0 : high]} with (item < 5);  // <--- Bad: 2**33 candidates
      bins other = {[5 : 10]};
    }
    listed: coverpoint v33 {
      bins b = {[0 : 33'h7fff_ffff], [low : 33'h1_8000_0000]} with (item == 1);  // <--- Bad: 2**32 + 1 candidates
    }
  endgroup

  // Of --coverage-max-bins 8
  covergroup cg_kept(int count);
    // 9 values, once duplicates are merged
    values: coverpoint v8 {
      bins b[] = {[0 : 5], [0 : 5], [3 : 8]} with (1);  // <--- Bad: bins
    }
    // 8 values, of 14 before duplicates are merged
    merged: coverpoint v8 {
      bins b[] = {[0 : 5], [0 : 5], [3 : 7]} with (1);
    }
    // 11 runs of values
    runs: coverpoint v8 {
      bins b = {[0 : 40]} with (item % 4 == 0);  // <--- Bad: runs
    }
    // 9 runs of one value
    single: coverpoint v8 {
      bins b = {1, 1, 1, 1, 1, 1, 1, 1, 1} with (1);
    }
    // A sized array keeps its duplicates
    fixed: coverpoint v8 {
      bins b[2] = {1, 1, 1, 1, 1, 1, 1, 1, 1} with (1);  // <--- Bad: runs
    }
    many: coverpoint v8 {
      bins b[9] = {[0 : 20]} with (1);  // <--- Bad: bins
    }
    counted: coverpoint v8 {
      bins b[count] = {[0 : 3]} with (1);  // <--- Bad: count
    }
  endgroup

  cg_candidates candidates_inst;
  // The limits apply to the values kept, whatever the order of the candidates
  covergroup cg_order;
    // 9 values, then a range holding them: one range of values
    listed: coverpoint v8 {
      bins b = {0, 2, 4, 6, 8, 10, 12, 14, 16, [0 : 16]} with (1);
    }
    // 8 values, each listed twice
    twice: coverpoint v8 {
      bins b[] = {[0 : 15], [0 : 15]} with (item % 2 == 0);
    }
  endgroup

  cg_kept kept_inst;
  cg_order order_inst;

  initial begin
    candidates_inst = new(33'h1_ffff_ffff, 33'h1_0000_0000);
    kept_inst = new(0);
    order_inst = new;
    v33 = 5;
    v8 = 1;
    candidates_inst.sample();
    kept_inst.sample();
    `checkr(candidates_inst.get_inst_coverage(), 100.0);
    `checkr(kept_inst.get_inst_coverage(), (100.0 / 8.0 + 100.0) / 2.0);
    v8 = 16;
    order_inst.sample();
    `checkr(order_inst.get_inst_coverage(), 50.0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
