// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test mixed bin types: single values and ranges

module t (/*AUTOARG*/);
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

    // Test multi-value list bin
    opcode = 8'h02; cg_inst.sample();  // load

    opcode = 8'h05; cg_inst.sample();  // store

    // Test range bin
    opcode = 8'h15; cg_inst.sample();  // arith

    opcode = 8'h80; cg_inst.sample();  // others

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
