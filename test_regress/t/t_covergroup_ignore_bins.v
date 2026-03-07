// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test ignore_bins - excluded from coverage

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (/*AUTOARG*/);
  /* verilator lint_off UNSIGNED */
  logic [3:0] data;

  covergroup cg;
    coverpoint data {
      bins low      = {[0:3]};
      bins mid      = {[4:7]};
      bins high     = {[8:11]};
      ignore_bins reserved = {[12:15]};  // Should not count toward coverage
    }
  endgroup

  cg cg_inst;

  initial begin
    cg_inst = new;

    // Initially 0% (0 of 3 regular bins)
    `checkr(cg_inst.get_inst_coverage(), 0.0);

    // Hit reserved bin - should still be 0%
    data = 13;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 0.0);

    // Hit low bin - now 33.33% (1 of 3)
    data = 1;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0 * (1.0/3.0));

    // Hit another reserved value - still 33.33%
    data = 15;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0 * (1.0/3.0));

    // Complete regular bins
    data = 5; cg_inst.sample();  // mid
    data = 10; cg_inst.sample(); // high
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
