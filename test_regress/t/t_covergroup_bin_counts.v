// DESCRIPTION: Verilator: Verilog Test module
//
// Tests bin counts, mixed bin types (single values, lists, ranges), and
// coverage database format (verifies coverage.dat contains covergroup entries).
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic [3:0] data;
  logic [7:0] opcode;
  logic signed [3:0] sdata;

  typedef struct packed {bit [7:0] value;} f_t;
  f_t f1;

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

  // cg_unbounded: open-ended bin range - '$' resolves to the coverpoint domain max (15 for 4-bit)
  covergroup cg_unbounded;
    cp: coverpoint data {
      bins lo     = {[0:9]};   // 1 bin: values 0..9
      bins others = {[10:$]};  // 1 bin: values 10..15 ($ == domain max)
    }
  endgroup

  // cg_unbounded_lo: open-ended LOWER bound - '$' resolves to the domain min (0)
  covergroup cg_unbounded_lo;
    cp: coverpoint data {
      bins start = {[$:5]};   // 1 bin: values 0..5  ($ == domain min) -> expr <= 5
      bins rest  = {[6:15]};
    }
  endgroup

  // cg_unbounded_all: both bounds open ('[$:$]' covers the entire domain -> always true)
  covergroup cg_unbounded_all;
    cp: coverpoint data {
      bins all = {[$:$]};  // 1 bin: every value
    }
  endgroup

  // cg_unbounded_signed: signed coverpoint with open-ended bounds in both directions
  covergroup cg_unbounded_signed;
    cp: coverpoint sdata {
      bins hi = {[2:$]};   // sdata >= 2   (signed >=)
      bins lo = {[$:-2]};  // sdata <= -2  (signed <=)
    }
  endgroup

  // cg_sel: coverpoint over a struct-member part-select expression (AstSel)
  covergroup cg_sel;
    cp: coverpoint f1.value[3:0] {  // low nibble only; upper bits ignored
      bins lo = {[0:7]};
      bins hi = {[8:15]};
    }
  endgroup

  cg                  cg_inst;
  cg_mixed            cg_mixed_inst;
  cg_db               cg_db_inst;
  cg_unbounded        cg_unbounded_inst;
  cg_unbounded_lo     cg_unbounded_lo_inst;
  cg_unbounded_all    cg_unbounded_all_inst;
  cg_unbounded_signed cg_unbounded_signed_inst;
  cg_sel              cg_sel_inst;

  initial begin
    cg_inst                  = new;
    cg_mixed_inst            = new;
    cg_db_inst               = new;
    cg_unbounded_inst        = new;
    cg_unbounded_lo_inst     = new;
    cg_unbounded_all_inst    = new;
    cg_unbounded_signed_inst = new;
    cg_sel_inst              = new;

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

    // Open-ended range: '$' upper bound covers values up to the domain max
    data = 5;  cg_unbounded_inst.sample();  // lo
    `checkr(cg_unbounded_inst.get_inst_coverage(), 50.0);
    data = 12; cg_unbounded_inst.sample();  // others ([10:$] covers 12)
    `checkr(cg_unbounded_inst.get_inst_coverage(), 100.0);

    // Open-ended lower bound: '$' min covers values down to 0
    data = 3;  cg_unbounded_lo_inst.sample();  // start ([$:5] covers 3)
    `checkr(cg_unbounded_lo_inst.get_inst_coverage(), 50.0);
    data = 10; cg_unbounded_lo_inst.sample();  // rest
    `checkr(cg_unbounded_lo_inst.get_inst_coverage(), 100.0);

    // Both-open range '[$:$]' matches any value
    data = 7;  cg_unbounded_all_inst.sample();  // all
    `checkr(cg_unbounded_all_inst.get_inst_coverage(), 100.0);

    // Signed open-ended bounds: '$' resolves to signed domain max/min
    sdata = 5;  cg_unbounded_signed_inst.sample();  // hi ([2:$] covers 5)
    `checkr(cg_unbounded_signed_inst.get_inst_coverage(), 50.0);
    sdata = -5; cg_unbounded_signed_inst.sample();  // lo ([$:-2] covers -5)
    `checkr(cg_unbounded_signed_inst.get_inst_coverage(), 100.0);

    // Part-select coverpoint: only the low nibble is sampled (upper bits ignored)
    f1.value = 8'h03; cg_sel_inst.sample();  // nibble 3 -> lo
    `checkr(cg_sel_inst.get_inst_coverage(), 50.0);
    f1.value = 8'hF9; cg_sel_inst.sample();  // nibble 9 -> hi (upper bits F ignored)
    `checkr(cg_sel_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
