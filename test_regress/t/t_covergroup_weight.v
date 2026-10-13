// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test option.weight and type_option.weight (IEEE 1800-2023 19.7, 19.11)

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit [1:0] a;  // 4 automatic bins
  bit [2:0] b;  // 8 automatic bins

  // Instance coverage is the average of the items, weighted by their option.weight
  covergroup cg_item;
    cpa: coverpoint a {
      option.weight = 3;
    }
    cpb: coverpoint b;
  endgroup

  // A zero weight removes an item from the instance coverage
  covergroup cg_item_zero;
    cpa: coverpoint a {
      option.weight = 0;
    }
    cpb: coverpoint b;
  endgroup

  // Nothing contributes, so the covergroup's option.weight decides between 0 and 100
  covergroup cg_all_zero;
    cpa: coverpoint a {
      option.weight = 0;
    }
    cpb: coverpoint b {
      option.weight = 0;
    }
  endgroup

  // Weights from a constructor argument and an expression, and a cross weight
  covergroup cg_cross(int w);
    option.weight = w + 1;
    cpa: coverpoint a {
      bins a0 = {0};
      bins a1 = {1};
      option.weight = w;
    }
    cpb: coverpoint b {
      bins b0 = {0};
      bins b1 = {1};
    }
    x: cross cpa, cpb{option.weight = 4;}
  endgroup

  // The covergroup's own weights do not scale its coverage, and an item's
  // type_option.weight only weighs type coverage merged over the instances
  covergroup cg_group;
    option.weight = 5;
    type_option.weight = 2;
    type_option.merge_instances = 0;
    cpa: coverpoint a {
      type_option.weight = 7;
    }
    cpb: coverpoint b {
      type_option.weight = 0;
    }
  endgroup

  // Type coverage is the average of the instances, weighted by their option.weight
  covergroup cg_type;
    cpa: coverpoint a;
  endgroup

  covergroup cg_type_w0;
    type_option.weight = 0;
    cpa: coverpoint a;
  endgroup

  // Never constructed
  covergroup cg_never;
    cpa: coverpoint a;
  endgroup

  covergroup cg_never_w0;
    type_option.weight = 0;
    cpa: coverpoint a;
  endgroup

  // Embedded covergroup weighted by a member of the enclosing class
  class Cls;
    int m_weight;
    covergroup cg_emb with function sample (bit [1:0] v);
      option.weight = m_weight;
      cpv: coverpoint v {
        option.weight = m_weight;
      }
      cpz: coverpoint v {
        bins zero = {0};
      }
    endgroup
    function new(int weight);
      m_weight = weight;
      cg_emb = new;
    endfunction
  endclass

  cg_item c_item = new;
  cg_item_zero c_item_zero = new;
  cg_all_zero c_all_zero = new;
  cg_cross c_cross = new(3);
  cg_group c_group = new;
  cg_type t1, t2, t3;
  cg_type_w0 u1;
  Cls obj;

  initial begin
    // Declaration values and defaults are visible (IEEE 1800-2023 19.10)
    `checkd(c_item.option.weight, 1);
    `checkd(c_item.type_option.weight, 1);
    `checkd(c_cross.option.weight, 4);
    `checkd(c_group.option.weight, 5);
    `checkd(c_group.type_option.weight, 2);
    `checkd(cg_group::type_option.weight, 2);
    `checkd(cg_never_w0::type_option.weight, 0);

    a = 0;
    b = 0;
    c_item.sample();
    c_item_zero.sample();
    c_all_zero.sample();
    c_cross.sample();
    c_group.sample();
    a = 1;
    c_item.sample();
    c_item_zero.sample();
    c_all_zero.sample();
    c_cross.sample();
    c_group.sample();

    // cpa: 2/4 automatic bins, cpb: 1/8 automatic bins
    `checkr(c_item.get_inst_coverage(), (3 * 50.0 + 12.5) / 4);
    `checkr(c_item_zero.get_inst_coverage(), 12.5);
    `checkr(c_all_zero.get_inst_coverage(), 0.0);
    `checkr(c_group.get_inst_coverage(), (50.0 + 12.5) / 2);
    // cpa: a0 and a1, cpb: b0, x: <a0,b0> and <a1,b0>
    `checkr(c_cross.get_inst_coverage(), (3 * 100.0 + 50.0 + 4 * 50.0) / 8);

    // A procedural option.weight takes effect immediately
    c_all_zero.option.weight = 0;
    `checkr(c_all_zero.get_inst_coverage(), 100.0);
    c_all_zero.option.weight = 1;
    `checkr(c_all_zero.get_inst_coverage(), 0.0);

    // An instance without coverage does not contribute to type coverage
    `checkr(cg_all_zero::get_coverage(), 0.0);
    `checkr(cg_item::get_coverage(), c_item.get_inst_coverage());
    `checkr(cg_group::get_coverage(), (50.0 + 12.5) / 2);

    t1 = new;
    t2 = new;
    t3 = new;
    t1.option.weight = 3;
    a = 0;
    t1.sample();
    a = 1;
    t1.sample();
    a = 2;
    t2.sample();
    // t1 50%, t2 25%, and t3 0%
    `checkr(cg_type::get_coverage(), (3 * 50.0 + 25.0 + 0.0) / 5);
    t3.option.weight = 0;
    `checkr(t3.get_coverage(), (3 * 50.0 + 25.0) / 4);
    // A destroyed instance still contributes, with its last weight
    t2 = null;
    `checkr(cg_type::get_coverage(), (25.0 + 3 * 50.0) / 4);
    t1.option.weight = 0;
    `checkr(cg_type::get_coverage(), 25.0);

    // With no contribution, type_option.weight decides between 0 and 100
    u1 = new;
    a = 0;
    u1.sample();
    `checkr(cg_type_w0::get_coverage(), 25.0);
    u1.option.weight = 0;
    `checkr(cg_type_w0::get_coverage(), 100.0);
    `checkr(cg_never::get_coverage(), 0.0);
    `checkr(cg_never_w0::get_coverage(), 100.0);
    cg_never::type_option.weight = 0;
    `checkr(cg_never::get_coverage(), 100.0);
    // type_option is shared by every instance
    cg_group::type_option.weight = 9;
    `checkd(c_group.type_option.weight, 9);

    obj = new(2);
    `checkd(obj.cg_emb.option.weight, 2);
    obj.cg_emb.sample(0);
    `checkr(obj.cg_emb.get_inst_coverage(), (2 * 25.0 + 100.0) / 3);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
