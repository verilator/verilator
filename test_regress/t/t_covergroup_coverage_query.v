// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test querying coverage values via get_inst_coverage

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (/*AUTOARG*/);
  /* verilator lint_off UNSIGNED */
  logic [3:0] data;

  covergroup cg;
    coverpoint data {
      bins low  = {[0:3]};
      bins mid  = {[4:7]};
      bins high = {[8:15]};
    }
  endgroup

  cg cg_inst;

  initial begin
    cg_inst = new;

    // Initially no coverage
    `checkr(cg_inst.get_inst_coverage(), 0.0);

    // Sample low bin - should be 33.33% (1 of 3 bins)
    data = 1;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0 * (1.0/3.0));

    // Sample mid bin - should be 66.67% (2 of 3 bins)
    data = 5;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0 * (2.0/3.0));

    // Sample high bin - should be 100% (3 of 3 bins)
    data = 10;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    // Sample again - coverage should still be 100%
    data = 2;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
