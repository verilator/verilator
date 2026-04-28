// DESCRIPTION: Verilator: Verilog Test module
//
// Tests bin counts, mixed bin types (single values, lists, ranges), and
// coverage database format (verifies coverage.dat contains covergroup entries).
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
  `define stop $stop
  `define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

  logic [3:0] data;
  logic [7:0] opcode;

  // cg: basic bin count tracking
  covergroup cg;
    coverpoint data {
      bins zero = {0};
      bins low  = {[1:3]};
    }
  endgroup

  // cg_mixed: mixed bin types - single values, multi-value lists, ranges
  covergroup cg_mixed;
    coverpoint opcode {
      bins nop   = {8'h00};
      bins load  = {8'h01, 8'h02, 8'h03};
      bins store = {8'h04, 8'h05};
      bins arith = {[8'h10:8'h1F]};
      bins other = {[8'h20:8'hFE]};
    }
  endgroup

  // cg_db: labeled coverpoint - verifies the coverage database records the correct hierarchy path
  covergroup cg_db;
    cp: coverpoint data {
      bins low  = {[0:3]};
      bins high = {[8:15]};
    }
  endgroup

  cg       cg_inst;
  cg_mixed cg_mixed_inst;
  cg_db    cg_db_inst;

  initial begin
    cg_inst       = new;
    cg_mixed_inst = new;
    cg_db_inst    = new;

    data = 0; cg_inst.sample();    // zero: 1
    `checkr(cg_inst.get_inst_coverage(), 50.0);
    data = 1; cg_inst.sample();    // low: 1
    `checkr(cg_inst.get_inst_coverage(), 100.0);
    data = 2; cg_inst.sample();    // low: 2
    data = 2; cg_inst.sample();    // low: 3

    opcode = 8'h00; cg_mixed_inst.sample();  // nop
    `checkr(cg_mixed_inst.get_inst_coverage(), 20.0);
    opcode = 8'h02; cg_mixed_inst.sample();  // load
    `checkr(cg_mixed_inst.get_inst_coverage(), 40.0);
    opcode = 8'h05; cg_mixed_inst.sample();  // store
    `checkr(cg_mixed_inst.get_inst_coverage(), 60.0);
    opcode = 8'h15; cg_mixed_inst.sample();  // arith
    `checkr(cg_mixed_inst.get_inst_coverage(), 80.0);
    opcode = 8'h80; cg_mixed_inst.sample();  // other
    `checkr(cg_mixed_inst.get_inst_coverage(), 100.0);

    data = 1;  cg_db_inst.sample();  // low
    `checkr(cg_db_inst.get_inst_coverage(), 50.0);
    data = 10; cg_db_inst.sample();  // high
    `checkr(cg_db_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
