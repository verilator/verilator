// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  covergroup cg with function sample(int a, int b);
    cpa: coverpoint a {
      bins zero = {0};
      bins one  = {1};
      bins hi   = {[2:3]};
    }
    cpb: coverpoint b {
      bins lo = {[0:1]};
      bins hi = {[2:3]};
    }
    cr: cross cpa, cpb {
      bins dup_subset = binsof(cpa) && binsof(cpa.one) && binsof(cpb.hi);
      bins dup_with   = binsof(cpa) && binsof(cpa) with (b < 2);
    }
  endgroup

  cg cov = new;

  initial begin
    cov.sample(0, 2);
    if (cov.cr.get_inst_coverage() != 0.0) $stop;

    cov.sample(1, 2);
    if (cov.cr.get_inst_coverage() != 50.0) $stop;

    cov.sample(3, 0);
    if (cov.cr.get_inst_coverage() != 100.0) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
