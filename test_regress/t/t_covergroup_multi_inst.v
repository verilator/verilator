// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test multiple covergroup instances with separate tracking

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (/*AUTOARG*/);
  /* verilator lint_off UNSIGNED */
  logic [3:0] data1, data2;

  covergroup cg;
    coverpoint data1 {
      bins low  = {[0:3]};
      bins high = {[4:15]};
    }
  endgroup

  cg cg_inst1, cg_inst2;

  initial begin
    cg_inst1 = new;
    cg_inst2 = new;

    // Initially both have 0% coverage
    `checkr(cg_inst1.get_inst_coverage(), 0.0);
    `checkr(cg_inst2.get_inst_coverage(), 0.0);

    // Sample different values in each instance
    data1 = 1;
    cg_inst1.sample();  // inst1: low covered (50%)
    `checkr(cg_inst1.get_inst_coverage(), 50.0);
    `checkr(cg_inst2.get_inst_coverage(), 0.0);

    data1 = 10;
    cg_inst2.sample();  // inst2: high covered (50%)
    `checkr(cg_inst1.get_inst_coverage(), 50.0);
    `checkr(cg_inst2.get_inst_coverage(), 50.0);

    // Complete coverage in inst1
    data1 = 8;
    cg_inst1.sample();  // inst1: both covered (100%)
    `checkr(cg_inst1.get_inst_coverage(), 100.0);
    `checkr(cg_inst2.get_inst_coverage(), 50.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
