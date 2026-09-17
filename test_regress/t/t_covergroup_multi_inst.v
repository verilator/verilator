// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Multiple instances of one covergroup type, sampled asymmetrically.  Pins both
// the merged .dat report (bins summed across instances) and each instance's
// get_inst_coverage().  The covergroup deliberately has two coverpoints with
// UNEQUAL normal-bin counts: that is the only shape where a per-item weighted
// average differs from the raw covered/total sum, so it is what makes a later
// change of the instance-coverage formula observable.

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((((gotv) - (expv)) > 0.001) || (((expv) - (gotv)) > 0.001)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic [1:0] a;
  logic [1:0] b;

  // cp_a has 4 normal bins, cp_b has 2 -- unequal on purpose (see header).
  covergroup cg_mi;
    cp_a: coverpoint a {
      bins a0 = {0};
      bins a1 = {1};
      bins a2 = {2};
      bins a3 = {3};
    }
    cp_b: coverpoint b {
      bins lo = {[0 : 1]};
      bins hi = {[2 : 3]};
    }
  endgroup

  cg_mi inst_full = new;  // every bin hit
  cg_mi inst_part = new;  // one bin of each coverpoint hit
  cg_mi inst_none = new;  // never sampled

  initial begin
    // inst_full: all four a values, both b halves
    for (int i = 0; i < 4; ++i) begin
      a = i[1:0];
      b = i[1:0];
      inst_full.sample();
    end

    // inst_part: a0 and lo only
    a = 0;
    b = 0;
    inst_part.sample();

    // inst_none is never sampled.

    // Today: raw covered/total over all bins of all items.
    // inst_full  6/6 -> 100.0
    // inst_part  2/6 ->  33.333  (weighted average over items would be 37.5)
    // inst_none  0/6 ->   0.0
    `checkr(inst_full.get_inst_coverage(), 100.0);
    `checkr(inst_part.get_inst_coverage(), 33.333);
    `checkr(inst_none.get_inst_coverage(), 0.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
