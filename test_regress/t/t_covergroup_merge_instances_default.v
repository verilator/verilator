// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test --coverage-merge-instances, the default of type_option.merge_instances (IEEE 1800-2023
// 19.11.3)

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv) do if ($sformatf("%0.2f", gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%0.2f exp=%s\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  // Merged by default, the items weigh by type_option.weight: 100
  covergroup cg_default with function sample (bit a, bit b);
    helper: coverpoint a {
      type_option.weight = 0;
    }
    checked: coverpoint b;
  endgroup
  // Its own type_option.merge_instances wins: 75
  covergroup cg_off with function sample (bit a, bit b);
    type_option.merge_instances = 0;
    helper: coverpoint a {
      type_option.weight = 0;
    }
    checked: coverpoint b;
  endgroup
  covergroup cg_on with function sample (bit a, bit b);
    type_option.merge_instances = 1;
    helper: coverpoint a {
      type_option.weight = 0;
    }
    checked: coverpoint b;
  endgroup
  // get_inst_coverage() is the instance's coverage only with option.get_inst_coverage: 75
  covergroup cg_inst with function sample (bit a, bit b);
    option.get_inst_coverage = 1;
    helper: coverpoint a {
      type_option.weight = 0;
    }
    checked: coverpoint b;
  endgroup
  // Merged, option.weight has no effect: 75
  covergroup cg_optw with function sample (bit a, bit b);
    helper: coverpoint a {
      option.weight = 0;
    }
    checked: coverpoint b;
  endgroup
  // Two instances hitting different bins: 100 merged, and 50 averaged
  covergroup cg_multi with function sample (bit a);
    cp: coverpoint a;
  endgroup
  covergroup cg_multi_off with function sample (bit a);
    type_option.merge_instances = 0;
    cp: coverpoint a;
  endgroup

  // An embedded covergroup: the objects hit different bins, 100 merged
  class C;
    bit v;
    covergroup cg_emb;
      cp: coverpoint v;
    endgroup
    function new();
      cg_emb = new;
    endfunction
  endclass

  cg_default d = new;
  cg_off off = new;
  cg_on on = new;
  cg_inst inst = new;
  cg_optw optw = new;
  cg_multi m1 = new;
  cg_multi m2 = new;
  cg_multi_off mo1 = new;
  cg_multi_off mo2 = new;
  C c1 = new;
  C c2 = new;

  initial begin
    d.sample(0, 0);
    d.sample(0, 1);
    off.sample(0, 0);
    off.sample(0, 1);
    on.sample(0, 0);
    on.sample(0, 1);
    inst.sample(0, 0);
    inst.sample(0, 1);
    optw.sample(0, 0);
    optw.sample(0, 1);
    m1.sample(0);
    m2.sample(1);
    mo1.sample(0);
    mo2.sample(1);
    c1.v = 0;
    c1.cg_emb.sample();
    c2.v = 1;
    c2.cg_emb.sample();

    `checkd(cg_default::type_option.merge_instances, 1'b1);
    `checkd(d.type_option.merge_instances, 1'b1);
    `checkd(cg_off::type_option.merge_instances, 1'b0);
    `checkd(cg_on::type_option.merge_instances, 1'b1);

    `checkp(d.get_coverage(), "100.00");
    `checkp(d.get_inst_coverage(), "100.00");
    `checkp(off.get_coverage(), "75.00");
    `checkp(off.get_inst_coverage(), "75.00");
    `checkp(on.get_coverage(), "100.00");
    `checkp(on.get_inst_coverage(), "100.00");
    `checkp(inst.get_coverage(), "100.00");
    `checkp(inst.get_inst_coverage(), "75.00");
    `checkp(optw.get_coverage(), "75.00");
    `checkp(optw.get_inst_coverage(), "75.00");
    `checkp(m1.get_coverage(), "100.00");
    `checkp(m1.get_inst_coverage(), "100.00");
    `checkp(m2.get_inst_coverage(), "100.00");
    `checkp(mo1.get_coverage(), "50.00");
    `checkp(mo1.get_inst_coverage(), "50.00");
    `checkp(mo2.get_inst_coverage(), "50.00");
    `checkp(c1.cg_emb.get_coverage(), "100.00");
    `checkp(c1.cg_emb.get_inst_coverage(), "100.00");
    `checkp(c2.cg_emb.get_inst_coverage(), "100.00");

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
