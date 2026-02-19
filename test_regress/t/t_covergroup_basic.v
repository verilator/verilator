// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%g exp=%g\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  int x;

  // 4 bins so coverage steps are 25% (exact in binary float)
  covergroup cg;
    cp: coverpoint x {
      bins b0 = {[0:3]};
      bins b1 = {[4:7]};
      bins b2 = {[8:11]};
      bins b3 = {[12:15]};
    }
  endgroup

  cg cg_inst;

  initial begin
    cg_inst = new;

    // Before sampling: 0%
    `checkr(cg_inst.get_inst_coverage(), 0.0);

    // Hit b0: 25%
    x = 1;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 25.0);

    // Hit b1: 50%
    x = 5;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 50.0);

    // Hit b2: 75%
    x = 9;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 75.0);

    // Hit b3: 100%
    x = 13;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    // Resample -- stays 100%
    x = 0;
    cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
