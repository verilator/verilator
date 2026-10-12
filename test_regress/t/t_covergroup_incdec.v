// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Increments and decrements in covergroup expressions, which are under no statement, as the
// covergroup evaluates them in its constructor or sample(): each evaluation increments once

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// An embedded covergroup writes members of its enclosing class (IEEE 1800-2023 19.4)
class Holder;
  bit [1:0] value;
  int count;
  int total;

  covergroup cg;
    cp: coverpoint value iff (count++ > 0) {bins b[] = {[0 : 3]};}  // Not value = 0
    tp: coverpoint (total += 2) {bins b[] = {2, 4, 6, 8};}
  endgroup

  function new();
    cg = new;
  endfunction
endclass

module t;
  bit [1:0] a;
  bit [1:0] b;
  int count;
  int down;
  logic [64:0] wide = 65'h1_ffff_ffff_ffff_fffe;
  real r = 0.1;
  int guard;
  int bin_guard;
  int and_count;
  int cond_count;
  int cross_guard;
  int sum;
  int step;
  int weight = 1;
  int filtered;
  int group_weight = 1;

  // A coverpoint's expression is evaluated once per sample
  covergroup cg_point;
    post: coverpoint count++ {bins b[] = {[0 : 7]};}  // 0, 1, 2
    pre: coverpoint --down {bins b[] = {[-3 : -1]};}  // -1, -2, -3
    wrap: coverpoint wide++ {bins b[] = {65'h1_ffff_ffff_ffff_fffe, 65'h1_ffff_ffff_ffff_ffff, 0};}
    exact: coverpoint r++ {
      bins first = {0.1};  // The value before the increment, exactly
      bins rest = {[1.0 : 3.0]};
    }
  endgroup

  // A guard is evaluated once per sample, if at all
  covergroup cg_guard;
    cp: coverpoint a iff (guard++ > 0) {bins b[] = {[0 : 3]};}  // Not a = 0
    bp: coverpoint a {bins b[] = {[0 : 3]} iff (bin_guard-- < 0);}  // Not a = 0
    ap: coverpoint a iff (a[0] && and_count++ >= 0) {bins b[] = {[0 : 3]};}  // a = 1, 3
    qp: coverpoint a iff (a[0] ? cond_count++ >= 0 : 0) {bins b[] = {[0 : 3]};}  // a = 1, 3
    np: coverpoint a iff ((sum += step++) > 0) {bins b[] = {[0 : 3]};}  // sum 0, 1, 3, 6
    aa: coverpoint a;
    bb: coverpoint b;
    xx: cross aa, bb{bins all = binsof (aa) iff (cross_guard++ > 0);}  // Not a = 0
  endgroup

  // A sample formal's value before its increment
  covergroup cg_formal with function sample (int seen);
    sp: coverpoint seen++ {bins b[] = {[0 : 3]};}  // 0, 1, 2
  endgroup

  // Options and filters are evaluated when an instance is constructed
  covergroup cg_construct;
    option.weight = group_weight++;
    cw: coverpoint a {
      option.weight = weight++;  // 1
      // How often a filter is evaluated is unpredictable (IEEE 1800-2023 19.5.1.1)
      bins b[] = cw with (filtered++ >= 0);  // All
    }
  endgroup

  cg_point point_inst = new;
  cg_guard guard_inst = new;
  cg_formal formal_inst = new;
  cg_construct construct_inst = new;
  Holder holder = new;

  initial begin
    `checkd(weight, 2);
    for (int i = 0; i < 4; ++i) begin
      a = 2'(i);
      b = 2'(i);
      if (i < 3) point_inst.sample();
      guard_inst.sample();
      if (i < 3) formal_inst.sample(i);
      construct_inst.sample();
      holder.value = a;
      holder.cg.sample();
    end
    `checkd(count, 3);
    `checkd(down, -3);
    `checkd(wide, 65'h1);
    `checkd(guard, 4);
    `checkd(bin_guard, -4);
    `checkd(and_count, 2);
    `checkd(cond_count, 2);
    `checkd(step, 4);
    `checkd(sum, 6);
    `checkd(cross_guard, 4);
    `checkd(weight, 2);
    `checkd(holder.count, 4);
    `checkd(holder.total, 8);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
