// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test get_inst_coverage() of coverpoints and crosses (IEEE 1800-2023 19.8, 19.11)

// verilog_format: off
`define stop $stop
`define checkp(gotv,expv) do if ($sformatf("%0.2f", gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%0.2f exp=%s\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  logic [3:0] a;
  int b;
  int cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
  end

  covergroup cg @(posedge clk);
    coverpoint a;
    coverpoint b {
      bins the_bins[5] = {[0 : 20]};
    }
    ab: cross a, b;
  endgroup

  cg the_cg = new;

  assign a = cyc[3:0];
  assign b = cyc;

  // On the falling edge, the rising edges have sampled the values 0 to cyc - 1
  always @(negedge clk) begin
    if (cyc == 5) begin
      `checkp(the_cg.a.get_inst_coverage(), "31.25");  // 5 of 16 bins
      `checkp(the_cg.b.get_inst_coverage(), "40.00");  // 2 of 5 bins
      `checkp(the_cg.ab.get_inst_coverage(), "6.25");  // 5 of 80 bins
    end
    else if (cyc == 15) begin
      `checkp(the_cg.a.get_inst_coverage(), "93.75");
      `checkp(the_cg.b.get_inst_coverage(), "80.00");
      `checkp(the_cg.ab.get_inst_coverage(), "18.75");
      // The empty parentheses of a built-in method call are optional (IEEE 1800-2023 5.13)
      `checkp(the_cg.a.get_inst_coverage, "93.75");
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // A coverpoint named as a formal argument, which a hierarchical name cannot reach (IEEE
  // 1800-2023 19.3), as the example of 19.8
  int xv, yv;
  covergroup cg_formal(int xb, yb, ref int x, y);
    coverpoint x {
      bins xbins[] = {[0 : 7]} with (item <= xb);
    }
    coverpoint y {
      bins ybins[] = {[0 : 7]} with (item <= yb);
    }
  endgroup
  cg_formal cv1 = new(1, 2, xv, yv);
  initial begin
    xv = 0;
    yv = 0;
    cv1.sample();
    xv = 1;
    yv = 2;
    cv1.sample();
    `checkp(cv1.x.get_inst_coverage(), "100.00");  // 2 of 2 bins
    `checkp(cv1.y.get_inst_coverage(), "66.67");  // 2 of 3 bins
    `checkp(cv1.get_inst_coverage(), "83.33");
    // Without parentheses, as a condition
    if (!cv1.x.get_inst_coverage) `stop;
    if (!cv1.get_inst_coverage) `stop;
    if (!cv1.get_coverage) `stop;
  end

  // An item without bins, none having a value of the coverpoint, does not count: 0, or 100 if
  // its weight is zero (IEEE 1800-2023 19.11.1)
  covergroup cg_no_bins with function sample (bit [3:0] v);
    weighted: coverpoint v {
      bins none = {[20 : 30]};
    }
    unweighted: coverpoint v {
      option.weight = 0;
      bins none = {[20 : 30]};
    }
  endgroup
  cg_no_bins no_bins = new;
  initial begin
    no_bins.sample(1);
    `checkp(no_bins.weighted.get_inst_coverage(), "0.00");
    `checkp(no_bins.unweighted.get_inst_coverage(), "100.00");
  end

`ifdef VERILATOR
  // A cross of a variable, so of an implicit coverpoint, which Verilator ignores, has no bins
  covergroup cg_ignored with function sample (bit v, bit w);
    cp: coverpoint v;
    // verilator lint_off COVERIGN
    x: cross cp, w;
    // verilator lint_on COVERIGN
  endgroup
  cg_ignored ignored = new;
  initial begin
    ignored.sample(0, 0);
    `checkp(ignored.cp.get_inst_coverage(), "50.00");
    `checkp(ignored.x.get_inst_coverage(), "0.00");
  end
`endif

  // A covergroup embedded in a class (IEEE 1800-2023 19.4), from outside and inside it
  class Cls;
    bit [2:0] m;
    covergroup cg_emb;
      cp: coverpoint m {
        bins lo = {[0 : 3]};
        bins hi = {[4 : 7]};
      }
    endgroup
    function new;
      cg_emb = new;
    endfunction
    function real cp_coverage();
      return cg_emb.cp.get_inst_coverage();
    endfunction
  endclass
  Cls obj = new;
  initial begin
    obj.m = 2;
    obj.cg_emb.sample();
    `checkp(obj.cg_emb.cp.get_inst_coverage(), "50.00");
    `checkp(obj.cp_coverage(), "50.00");
  end
endmodule
