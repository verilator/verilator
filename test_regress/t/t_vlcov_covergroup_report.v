// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Covergroup coverage in verilator_coverage reports is as get_coverage() computes it
// (IEEE 1800-2023 19.11), not a ratio of bins

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) > (expv) + 0.001 || (gotv) < (expv) - 0.001) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A covergroup of a specialization is named with the values of its parameters, whose dots split
// the name into no nodes of the report, nor do the escaped quote and parenthesis of a string
// value, which shows as written, though the coverage file escapes its quotes and '%': 50
module spec #(
    parameter real R = 0.0,
    parameter string S = ""
);
  covergroup cg with function sample (bit v);
    cp: coverpoint v;
  endgroup
  cg inst = new;
endmodule

module t;
  // Ignore, illegal and default bins are not coverable: 100
  covergroup excluded with function sample (int value);
    cp: coverpoint value {
      bins hit = {0};
      ignore_bins ignored = {1};
      illegal_bins illegal = {2};
      bins other = default;
    }
  endgroup
  // The average of the coverpoints, 50 and 25: 37.5
  covergroup unequal with function sample (bit a, bit [1:0] b);
    cp_a: coverpoint a;
    cp_b: coverpoint b;
  endgroup
  // A coverpoint of zero weight does not count: 100
  covergroup weighted with function sample (bit a, bit b);
    cp_a: coverpoint a {
      option.weight = 0;
      type_option.weight = 0;
    }
    cp_b: coverpoint b;
  endgroup
  // option.weight weighs the coverpoints, as in get_coverage(): 100, then 75
  covergroup instance_weight with function sample (bit a, bit b);
    cp_a: coverpoint a {
      option.weight = 0;
    }
    cp_b: coverpoint b;
  endgroup
  covergroup type_weight with function sample (bit a, bit b);
    cp_a: coverpoint a {
      type_option.weight = 0;
    }
    cp_b: coverpoint b;
  endgroup
  // Merging the instances, type_option.weight weighs the coverpoints, as in get_coverage(): 100
  covergroup type_merged with function sample (bit a, bit b);
    type_option.merge_instances = 1;
    cp_a: coverpoint a {
      type_option.weight = 0;
    }
    cp_b: coverpoint b;
  endgroup
  // And option.weight does not; instances hitting distinct bins merge as in get_coverage(): 75
  covergroup inst_merged with function sample (bit a, bit b);
    type_option.merge_instances = 1;
    cp_a: coverpoint a {
      option.weight = 0;
    }
    cp_b: coverpoint b;
  endgroup
  // A bin is covered once hit option.at_least times: 50
  covergroup threshold with function sample (bit a);
    cp: coverpoint a {
      option.at_least = 2;
    }
  endgroup
  // A cross is an item, of its weight, whose ignored bins do not count: 50, 25, and 25 thrice:
  // 30
  covergroup crossed with function sample (bit a, bit [1:0] b);
    cp_a: coverpoint a;
    cp_b: coverpoint b;
    x: cross cp_a, cp_b{
      option.weight = 3;
      ignore_bins ignored = binsof (cp_a) intersect {1};
    }
  endgroup
  // Cross bins named by joining their coverpoints' bins would collide: those of 'a' and 'b_x_c',
  // and of 'a_x_b' and 'c'.  Named by tuples, they do not: 100, 100 and 75: 91.67
  covergroup collide with function sample (bit u, bit v);
    p: coverpoint u {
      bins a = {0};
      bins a_x_b = {1};
    }
    q: coverpoint v {
      bins c = {0};
      bins b_x_c = {1};
    }
    x: cross p, q;
  endgroup
  // Weighs as its type_option.weight, a coverpoint whose option.weight is not a constant, and
  // so may differ in the instances the coverage database merges: 50 three times, and 100: 62.5,
  // where get_coverage() averages the instances: 50
  covergroup varying(int w) with function sample (bit v, bit u);
    cp: coverpoint v {
      option.weight = w;
      type_option.weight = 3;
    }
    cq: coverpoint u;
  endgroup
  // Without coverable bins: 0, so not counted in the coverage of the covergroups, and a
  // coverpoint of zero weight without them, 100
  covergroup empty with function sample (bit a);
    cp: coverpoint a {
      ignore_bins ignored = {[0 : 1]};
    }
    unweighted: coverpoint a {
      option.weight = 0;
      ignore_bins ignored = {[0 : 1]};
    }
  endgroup
  // Of zero weight, without coverable bins: 100
  covergroup free with function sample (bit a);
    type_option.weight = 0;
    cp: coverpoint a {
      ignore_bins ignored = {[0 : 1]};
    }
  endgroup
  // Of three times the weight of the others in the coverage of the covergroups: 50
  covergroup heavy with function sample (bit a);
    type_option.weight = 3;
    cp: coverpoint a;
  endgroup
  // The coverage database merges the bins of the instances: 100, where get_coverage() averages
  // the instances: 50
  covergroup merged with function sample (bit a);
    cp: coverpoint a;
  endgroup

  // Covergroups of a name in distinct classes are distinct types, each of its own bins: 100 and
  // 0, where a single type would average its instances: 50
  class First;
    bit v;
    covergroup twin;
      cp: coverpoint v {
        bins hit = {0};
        bins miss = {1};
      }
    endgroup
    function new;
      twin = new;
    endfunction
  endclass
  class Second;
    bit v;
    covergroup twin;
      cp: coverpoint v {
        bins hit = {0};
        bins miss = {1};
      }
    endgroup
    function new;
      twin = new;
    endfunction
  endclass

  // Classes declared in the iterations of a generate loop are distinct classes, so their
  // covergroups are distinct types, named with each generate block: 100 and 0
  for (genvar i = 0; i < 2; ++i) begin : gen
    class Gen;
      bit v;
      covergroup cg;
        cp: coverpoint v;
      endgroup
      function new;
        cg = new;
      endfunction
    endclass
    Gen obj = new;
  end

  excluded excluded_inst = new;
  unequal unequal_inst = new;
  weighted weighted_inst = new;
  instance_weight instance_weight_inst = new;
  type_weight type_weight_inst = new;
  type_merged type_merged_inst = new;
  inst_merged inst_merged_first = new;
  inst_merged inst_merged_second = new;
  threshold threshold_inst = new;
  crossed crossed_inst = new;
  empty empty_inst = new;
  free free_inst = new;
  heavy heavy_inst = new;
  merged merged_first = new;
  merged merged_second = new;
  collide collide_inst = new;
  varying varying_none = new(0);
  varying varying_two = new(2);
  First first = new;
  Second second = new;
  spec #(0.5, "a.\"(b%22") sp ();

  initial begin
    excluded_inst.sample(0);
    unequal_inst.sample(0, 0);
    weighted_inst.sample(0, 0);
    weighted_inst.sample(0, 1);
    instance_weight_inst.sample(0, 0);
    instance_weight_inst.sample(0, 1);
    type_weight_inst.sample(0, 0);
    type_weight_inst.sample(0, 1);
    type_merged_inst.sample(0, 0);
    type_merged_inst.sample(0, 1);
    inst_merged_first.sample(0, 0);
    inst_merged_second.sample(1, 0);
    threshold_inst.sample(0);
    threshold_inst.sample(0);
    threshold_inst.sample(1);
    crossed_inst.sample(0, 0);
    empty_inst.sample(0);
    free_inst.sample(0);
    heavy_inst.sample(0);
    merged_first.sample(0);
    merged_second.sample(1);
    collide_inst.sample(0, 0);
    collide_inst.sample(0, 1);
    collide_inst.sample(1, 1);
    varying_none.sample(0, 0);
    varying_two.sample(0, 1);
    first.v = 0;
    first.twin.sample();
    first.v = 1;
    first.twin.sample();
    gen[0].obj.v = 0;
    gen[0].obj.cg.sample();
    gen[0].obj.v = 1;
    gen[0].obj.cg.sample();
    sp.inst.sample(1);
    `checkr(excluded_inst.get_coverage(), 100.0);
    `checkr(unequal_inst.get_coverage(), 37.5);
    `checkr(weighted_inst.get_coverage(), 100.0);
    `checkr(instance_weight_inst.get_coverage(), 100.0);
    `checkr(type_weight_inst.get_coverage(), 75.0);
    `checkr(type_merged_inst.get_coverage(), 100.0);
    `checkr(inst_merged_first.get_coverage(), 75.0);
    `checkr(threshold_inst.get_coverage(), 50.0);
    `checkr(crossed_inst.get_coverage(), 30.0);
    `checkr(empty_inst.get_coverage(), 0.0);
    `checkr(free_inst.get_coverage(), 100.0);
    `checkr(heavy_inst.get_coverage(), 50.0);
    `checkr(merged_first.get_coverage(), 50.0);
    `checkr(collide_inst.get_coverage(), 275.0 / 3);
    `checkr(varying_none.get_coverage(), 50.0);
    `checkr(first.twin.get_coverage(), 100.0);
    `checkr(second.twin.get_coverage(), 0.0);
    `checkr(gen[0].obj.cg.get_coverage(), 100.0);
    `checkr(gen[1].obj.cg.get_coverage(), 0.0);
    `checkr(sp.inst.get_coverage(), 50.0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
