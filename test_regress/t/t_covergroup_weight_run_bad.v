// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Coverage weights that are negative only at run time (IEEE 1800-2023 19.7): each
// negative value is reported once, and counts as zero

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit [1:0] a;  // 4 automatic bins
  bit [2:0] b;  // 8 automatic bins

  covergroup cg_item(int wa, int wb);
    cpa: coverpoint a {
      option.weight = wa;
    }
    cpb: coverpoint b {
      option.weight = wb;  // <--- Bad: negative at run time
    }
  endgroup

  covergroup cg_cross(int w);
    cpa: coverpoint a {
      bins a0 = {0};
      bins a1 = {1};
    }
    cpb: coverpoint b {
      bins b0 = {0};
      bins b1 = {1};
    }
    x: cross cpa, cpb{option.weight = w;}  // <--- Bad: negative at run time
  endgroup

  // A covergroup's own weights are reported at its declaration
  covergroup cg_inst(int w);  // <--- Bad: option.weight negative at run time
    option.weight = w;
    cpa: coverpoint a;
  endgroup

  covergroup cg_empty;  // <--- Bad: option.weight negative at run time
  endgroup

  covergroup cg_never;  // <--- Bad: type_option.weight negative at run time
    cpa: coverpoint a;
  endgroup

  cg_item c_cancel, c_over;
  cg_cross c_cross;
  cg_inst d1, d2;
  cg_empty e1;

  initial begin
    // Item weights summing to zero, or nearly, would otherwise give a zero
    // denominator, or coverage outside 0..100
    c_cancel = new(2, -2);
    c_over = new(3, -2);
    c_cross = new(-1);
    a = 0;
    b = 0;
    c_cancel.sample();
    c_over.sample();
    c_cross.sample();
    a = 1;
    c_cancel.sample();
    c_over.sample();
    c_cross.sample();
    // cpa: 2/4 automatic bins, and cpb weighs nothing
    `checkr(c_cancel.get_inst_coverage(), 50.0);
    `checkr(c_over.get_inst_coverage(), 50.0);
    // cpa: a0 and a1, cpb: b0, and x weighs nothing
    `checkr(c_cross.get_inst_coverage(), (100.0 + 50.0) / 2);

    // Reported by the constructor
    d1 = new(-1);
    d2 = new(1);
    a = 0;
    d1.sample();
    a = 1;
    d1.sample();
    a = 2;
    d2.sample();
    // d1 50% weighs nothing, d2 25%
    `checkr(cg_inst::get_coverage(), 25.0);
    // A procedural assignment is reported when coverage is next computed, once
    d2.option.weight = -3;
    `checkr(d2.get_inst_coverage(), 25.0);
    `checkr(cg_inst::get_coverage(), 0.0);
    d2.option.weight = -4;
    `checkr(cg_inst::get_coverage(), 0.0);
    d2.option.weight = 2;
    `checkr(cg_inst::get_coverage(), 25.0);
    // A destroyed instance keeps weighing nothing
    d1 = null;
    `checkr(cg_inst::get_coverage(), 25.0);

    // With nothing to cover, a negative weight decides as a zero weight
    e1 = new;
    e1.option.weight = -5;
    `checkr(e1.get_inst_coverage(), 100.0);
    `checkr(e1.get_inst_coverage(), 100.0);
    cg_never::type_option.weight = -6;
    `checkr(cg_never::get_coverage(), 100.0);
    `checkr(cg_never::get_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
