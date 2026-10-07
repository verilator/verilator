// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test type_option.merge_instances (IEEE 1800-2023 19.7.1, 19.11.3)

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv) do if ($sformatf("%0.2f", gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%0.2f exp=%s\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);
  int cyc = 0;

  // Without merge_instances, type coverage averages the instances, whose items weigh by
  // option.weight, so helper's type_option.weight has no effect: 75
  covergroup cg_avg with function sample (bit a, bit b);
    helper: coverpoint a {
      type_option.weight = 0;
    }
    checked: coverpoint b;
  endgroup
  // Merged, the items weigh by type_option.weight: 100, and get_inst_coverage() returns
  // get_coverage() (Table 19-1)
  covergroup cg_merged with function sample (bit a, bit b);
    type_option.merge_instances = 1;
    helper: coverpoint a {
      type_option.weight = 0;
    }
    checked: coverpoint b;
  endgroup
  // With option.get_inst_coverage, get_inst_coverage() is the instance's coverage: 75
  covergroup cg_inst with function sample (bit a, bit b);
    type_option.merge_instances = 1;
    option.get_inst_coverage = 1;
    helper: coverpoint a {
      type_option.weight = 0;
    }
    checked: coverpoint b;
  endgroup
  // Merged, option.weight has no effect: 75, and the instance's coverage: 100
  covergroup cg_opt with function sample (bit a, bit b);
    type_option.merge_instances = 1;
    option.get_inst_coverage = 1;
    helper: coverpoint a {
      option.weight = 0;
    }
    checked: coverpoint b;
  endgroup
  // As the example of 19.11.3: bins b[0], b[1] and b[1], b[2] merge by name, 2 of 3 covered
  covergroup cg_union(int l, h) with function sample (int a);
    type_option.merge_instances = 1;
    option.get_inst_coverage = 1;
    coverpoint a {
      bins b[] = {[0 : 3]} with (item >= l && item <= h);
    }
  endgroup
  // The same averaged: 100 and 50
  covergroup cg_union_avg(int l, h) with function sample (int a);
    coverpoint a {
      bins b[] = {[0 : 3]} with (item >= l && item <= h);
    }
  endgroup
  // The counts of a merged bin sum: at_least 2, and each instance hits auto[0] once: 50
  covergroup cg_sum with function sample (bit a);
    type_option.merge_instances = 1;
    cp: coverpoint a {
      option.at_least = 2;
    }
  endgroup
  // A cross weighs by type_option.weight: (50 + 25 + 3 * 12.5) / 5
  covergroup cg_cross with function sample (bit a, bit [1:0] b);
    type_option.merge_instances = 1;
    cp_a: coverpoint a;
    cp_b: coverpoint b;
    x: cross cp_a, cp_b{type_option.weight = 3;}
  endgroup
  // And not by option.weight: (50 + 25 + 12.5) / 3
  covergroup cg_cross_opt with function sample (bit a, bit [1:0] b);
    type_option.merge_instances = 1;
    cp_a: coverpoint a;
    cp_b: coverpoint b;
    x: cross cp_a, cp_b{option.weight = 3;}
  endgroup
  // Cross bins merge by name: (100 + 100 + 50) / 3
  covergroup cg_cross_union with function sample (bit a, bit b);
    type_option.merge_instances = 1;
    cp_a: coverpoint a;
    cp_b: coverpoint b;
    x: cross cp_a, cp_b;
  endgroup
  // An explicit cross bin named as an automatic bin's bins joined with _x_ stays apart from it:
  // 1 of 4 covered
  covergroup cg_cross_named with function sample (bit a, bit b);
    type_option.merge_instances = 1;
    cp_a: coverpoint a {
      type_option.weight = 0;
    }
    cp_b: coverpoint b {
      type_option.weight = 0;
    }
    x: cross cp_a, cp_b{
      bins auto_1_x_auto_1 = binsof (cp_a) intersect {0} && binsof (cp_b) intersect {0};
    }
  endgroup
  // Automatic cross bins stay apart though their bins' names joined with _x_ collide, <a,b_x_c>
  // and <a_x_b,c>: 1 of 4 covered
  covergroup cg_cross_joined with function sample (bit x, bit y);
    type_option.merge_instances = 1;
    p: coverpoint x {
      type_option.weight = 0;
      bins a = {0};
      bins a_x_b = {1};
    }
    q: coverpoint y {
      type_option.weight = 0;
      bins b_x_c = {0};
      bins c = {1};
    }
    xy: cross p, q;
  endgroup
  // Ignored cross bins are not coverable: 1 of 2 covered
  covergroup cg_cross_ignore with function sample (bit a, bit b);
    type_option.merge_instances = 1;
    cp_a: coverpoint a {
      type_option.weight = 0;
    }
    cp_b: coverpoint b {
      type_option.weight = 0;
    }
    x: cross cp_a, cp_b{ignore_bins skip = binsof (cp_a) intersect {1};}
  endgroup
  // Every item of type weight zero: 0, or 100 if the covergroup's type weight is zero too
  covergroup cg_zero with function sample (bit a);
    type_option.merge_instances = 1;
    cp: coverpoint a {
      type_option.weight = 0;
    }
  endgroup
  covergroup cg_zero_type with function sample (bit a);
    type_option.merge_instances = 1;
    type_option.weight = 0;
    cp: coverpoint a {
      type_option.weight = 0;
    }
  endgroup
  // The bins of an instance that has died still count: 100
  covergroup cg_dead with function sample (bit a);
    type_option.merge_instances = 1;
    cp: coverpoint a;
  endgroup
  // The bins of an instance that has died still count, though no live instance has them: b[0]
  // and b[1] hit by the instance that dies, b[2] and b[3] of the live one, 3 of 4 covered
  covergroup cg_dead_union(int l, h) with function sample (int a);
    type_option.merge_instances = 1;
    coverpoint a {
      bins b[] = {[0 : 3]} with (item >= l && item <= h);
    }
  endgroup
  // Merged by an assignment during simulation (IEEE 1800-2023 19.7.1): 50 averaged, and 100
  // merged, with the bins of an instance that died before
  covergroup cg_proc with function sample (bit a);
    cp: coverpoint a;
  endgroup

  cg_avg avg = new;
  cg_merged merged = new;
  cg_inst inst = new;
  cg_opt opt = new;
  cg_union union_1 = new(0, 1);
  cg_union union_2 = new(1, 2);
  cg_union_avg union_avg_1 = new(0, 1);
  cg_union_avg union_avg_2 = new(1, 2);
  cg_sum sum_1 = new;
  cg_sum sum_2 = new;
  cg_cross cross_w = new;
  cg_cross_opt cross_opt = new;
  cg_cross_union cross_union_1 = new;
  cg_cross_union cross_union_2 = new;
  cg_cross_named cross_named = new;
  cg_cross_joined cross_joined = new;
  cg_cross_ignore cross_ignore = new;
  cg_zero zero = new;
  cg_zero_type zero_type = new;
  cg_dead dead_1 = new;
  cg_dead dead_2 = new;
  cg_dead_union dead_union_1 = new(2, 3);
  cg_dead_union dead_union_2 = new(0, 1);
  cg_proc proc_1 = new;
  cg_proc proc_2 = new;

  initial begin
    avg.sample(0, 0);
    avg.sample(0, 1);
    `checkp(avg.get_coverage(), "75.00");
    `checkp(avg.get_inst_coverage(), "75.00");

    merged.sample(0, 0);
    merged.sample(0, 1);
    `checkp(merged.get_coverage(), "100.00");
    `checkp(merged.get_inst_coverage(), "100.00");

    inst.sample(0, 0);
    inst.sample(0, 1);
    `checkp(inst.get_coverage(), "100.00");
    `checkp(inst.get_inst_coverage(), "75.00");

    opt.sample(0, 0);
    opt.sample(0, 1);
    `checkp(opt.get_coverage(), "75.00");
    `checkp(opt.get_inst_coverage(), "100.00");

    union_1.sample(0);
    union_1.sample(1);
    union_2.sample(1);
    `checkp(union_1.get_coverage(), "66.67");
    `checkp(union_1.get_inst_coverage(), "100.00");
    `checkp(union_2.get_inst_coverage(), "50.00");

    union_avg_1.sample(0);
    union_avg_1.sample(1);
    union_avg_2.sample(1);
    `checkp(union_avg_1.get_coverage(), "75.00");

    sum_1.sample(0);
    sum_2.sample(0);
    `checkp(sum_1.get_coverage(), "50.00");
    `checkp(sum_1.get_inst_coverage(), "50.00");

    cross_w.sample(0, 0);
    `checkp(cross_w.get_coverage(), "22.50");

    cross_opt.sample(0, 0);
    `checkp(cross_opt.get_coverage(), "29.17");

    cross_union_1.sample(0, 0);
    cross_union_2.sample(1, 1);
    `checkp(cross_union_1.get_coverage(), "83.33");

    cross_named.sample(0, 0);
    `checkp(cross_named.get_coverage(), "25.00");

    cross_joined.sample(0, 0);
    `checkp(cross_joined.get_coverage(), "25.00");

    cross_ignore.sample(0, 0);
    `checkp(cross_ignore.get_coverage(), "50.00");

    zero.sample(0);
    `checkp(zero.get_coverage(), "0.00");
    zero_type.sample(0);
    `checkp(zero_type.get_coverage(), "100.00");

    dead_1.sample(0);
    dead_2.sample(1);
    dead_union_1.sample(2);
    dead_union_2.sample(0);
    dead_union_2.sample(1);
    proc_1.sample(0);
    proc_2.sample(1);
  end

  // Instances die once their evaluation ends, so after a clock edge
  function int retired_dead();
    retired_dead = $c32(
        "Verilated::threadContextp()->covergroupRegistryp()->retiredInstanceCount(\"t.cg_dead\")");
  endfunction
  function int retired_proc();
    retired_proc = $c32(
        "Verilated::threadContextp()->covergroupRegistryp()->retiredInstanceCount(\"t.cg_proc\")");
  endfunction

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) begin
      dead_2 = null;
      dead_union_2 = null;
      proc_2 = null;
    end
    else if (cyc == 3) begin
      `checkd(retired_dead(), 1);
      `checkp(dead_1.get_coverage(), "100.00");
      `checkp(dead_union_1.get_coverage(), "75.00");

      `checkd(retired_proc(), 1);
      `checkp(proc_1.get_coverage(), "50.00");
      `checkp(proc_1.get_inst_coverage(), "50.00");
      cg_proc::type_option.merge_instances = 1;
      `checkp(proc_1.get_coverage(), "100.00");
      `checkp(proc_1.get_inst_coverage(), "100.00");
      proc_1.type_option.merge_instances = 0;
      `checkp(proc_1.get_coverage(), "50.00");

      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
