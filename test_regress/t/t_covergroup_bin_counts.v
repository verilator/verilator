// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test viewing individual bin hit counts

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (/*AUTOARG*/);
  /* verilator lint_off UNSIGNED */
  logic [3:0] data;

  covergroup cg;
    coverpoint data {
      bins zero  = {0};
      bins low   = {[1:3]};
      bins mid   = {[4:7]};
      bins high  = {[8:15]};
    }
  endgroup

  cg cg_inst;

  initial begin
    cg_inst = new;

    // Sample various values with different frequencies
    data = 0;  cg_inst.sample();  // zero: 1
    data = 1;  cg_inst.sample();  // low: 1
    data = 2;  cg_inst.sample();  // low: 2
    data = 2;  cg_inst.sample();  // low: 3
    data = 5;  cg_inst.sample();  // mid: 1
    data = 10; cg_inst.sample();  // high: 1

    // Verify coverage is 100% (all 4 bins hit)
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
