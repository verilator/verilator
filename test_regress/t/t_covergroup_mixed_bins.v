// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test mixed bin types: single values and ranges

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (/*AUTOARG*/);
  /* verilator lint_off UNSIGNED */
  logic [7:0] opcode;

  covergroup cg;
    coverpoint opcode {
      bins nop      = {8'h00};
      bins load     = {8'h01, 8'h02, 8'h03};
      bins store    = {8'h04, 8'h05};
      bins arith    = {[8'h10:8'h1F]};
      bins others   = {[8'h20:8'hFE]};  // Avoid 0xFF to prevent CMPCONST warning
    }
  endgroup

  cg cg_inst;

  initial begin
    cg_inst = new;

    // Test single value bins
    opcode = 8'h00; cg_inst.sample();  // nop
    `checkr(cg_inst.get_inst_coverage(), 20.0);

    // Test multi-value list bin
    opcode = 8'h02; cg_inst.sample();  // load
    `checkr(cg_inst.get_inst_coverage(), 40.0);

    opcode = 8'h05; cg_inst.sample();  // store
    `checkr(cg_inst.get_inst_coverage(), 60.0);

    // Test range bin
    opcode = 8'h15; cg_inst.sample();  // arith
    `checkr(cg_inst.get_inst_coverage(), 80.0);

    opcode = 8'h80; cg_inst.sample();  // others
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
