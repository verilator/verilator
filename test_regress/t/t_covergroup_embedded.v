// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Embedded covergroups whose coverage constructs reference members of the
// enclosing class.  IEEE 1800-2023 19.4 allows class members in coverpoint
// expressions, conditional guards, option initialization, and other coverage
// constructs; 8.11 also allows 'this' within an embedded covergroup.

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

bit [3:0] global_value;

covergroup GlobalCg;
  cp_global: coverpoint global_value;
endgroup

class GlobalCgHolder;
  GlobalCg cg;

  function new();
    cg = new;
  endfunction
endclass

class Inner;
  bit [3:0] value;
endclass

class Transaction;
  bit [7:0] operand_a;
  bit [1:0] operand_b;
  Inner inner;
endclass

class Monitor;
  bit [3:0] addr;  // Direct member of the enclosing class
  bit enable;
  Transaction trx;  // Class-handle member of the enclosing class

  covergroup mon_cg;
    cp_addr: coverpoint addr {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
    cp_enabled: coverpoint addr iff (enable) {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
    cp_op_a: coverpoint trx.operand_a {bins lo = {[0 : 127]}; bins hi = {[128 : 255]};}
    cp_op_b: coverpoint trx.operand_b;
    cp_inner: coverpoint trx.inner.value {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
    addr_x_op_b: cross cp_addr, cp_op_b;
  endgroup

  function new();
    trx = new;
    trx.inner = new;
    mon_cg = new;
  endfunction

  function void observe(bit [3:0] a, bit [7:0] oa, bit [1:0] ob, bit [3:0] iv);
    addr = a;
    enable = a[3];
    trx.operand_a = oa;
    trx.operand_b = ob;
    trx.inner.value = iv;
    mon_cg.sample();
  endfunction
endclass

class BranchMonitor;
  bit [2:0] value;

  covergroup branch_cg;
    cp_branch: coverpoint value {bins lo = {[0 : 3]}; bins hi = {[4 : 7]};}
  endgroup

  function new(bit choose_first);
    if (choose_first) begin
      branch_cg = new;
    end
    else begin
      branch_cg = new;
    end
  endfunction

  function void observe(bit [2:0] v);
    value = v;
    branch_cg.sample();
  endfunction
endclass

class BaseMonitor;
  bit [3:0] inherited_value;
endclass

class DerivedMonitor extends BaseMonitor;
  covergroup derived_cg;
    cp_inherited: coverpoint inherited_value {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
  endgroup

  function new();
    derived_cg = new;
  endfunction

  function void observe(bit [3:0] v);
    inherited_value = v;
    derived_cg.sample();
  endfunction
endclass

class ThisMonitor;
  bit [3:0] current;

  covergroup this_cg;
    cp_this: coverpoint this.current iff (this == this) {
      bins lo = {[0 : 7]};
      bins hi = {[8 : 15]};
    }
  endgroup

  function new();
    this_cg = new;
  endfunction

  function void observe(bit [3:0] v);
    current = v;
    this_cg.sample();
  endfunction
endclass

class CopyMonitor;
  bit [3:0] value;

  covergroup copy_cg;
    cp_copy: coverpoint value {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
  endgroup

  function new();
    copy_cg = new;
  endfunction

  function void observe(bit [3:0] v);
    value = v;
    copy_cg.sample();
  endfunction
endclass

class CloneBaseMonitor;
  bit [3:0] base_value;

  covergroup cg;
    cp_base: coverpoint base_value;
  endgroup

  function new();
    cg = new;
  endfunction
endclass

class CloneDerivedMonitor extends CloneBaseMonitor;
  bit [3:0] derived_value;

  covergroup cg;
    cp_derived: coverpoint derived_value;
  endgroup

  function new();
    cg = new;
  endfunction
endclass

class StaticMonitor;
  static bit [3:0] static_value;
  bit [3:0] instance_value;

  covergroup static_cg;
    cp_static: coverpoint static_value {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
    cp_instance: coverpoint instance_value {bins lo = {[0 : 7]}; bins hi = {[8 : 15]};}
  endgroup

  function new();
    static_cg = new;
  endfunction

  function void observe(bit [3:0] v);
    static_value = v;
    instance_value = v;
    static_cg.sample();
  endfunction
endclass

class StaticOnlyMonitor;
  static bit [3:0] static_value;

  covergroup static_only_cg;
    cp_static_only: coverpoint static_value iff (this == this) {
      bins lo = {[0 : 7]};
      bins hi = {[8 : 15]};
    }
  endgroup

  function new();
    static_only_cg = new;
  endfunction

  function void observe(bit [3:0] v);
    static_value = v;
    static_only_cg.sample();
  endfunction
endclass

module t;
  Monitor mon;
  BranchMonitor branch_a;
  BranchMonitor branch_b;
  DerivedMonitor derived;
  ThisMonitor this_mon;
  CopyMonitor copy_src;
  CopyMonitor copy_dst;
  GlobalCgHolder global_src;
  GlobalCgHolder global_dst;
  CloneDerivedMonitor clone_src;
  CloneDerivedMonitor clone_dst;
  CloneBaseMonitor clone_base_view;
  StaticMonitor static_mon;
  StaticOnlyMonitor static_only_mon;
  int i;

  initial begin
    mon = new;
    branch_a = new(1);
    branch_b = new(0);
    derived = new;
    this_mon = new;
    copy_src = new;
    global_src = new;
    clone_src = new;
    static_mon = new;
    static_only_mon = new;

    for (i = 0; i < 16; ++i) begin
      mon.observe(i[3:0], i[7:0] * 17, i[1:0], i[3:0]);
      derived.observe(i[3:0]);
      this_mon.observe(i[3:0]);
      static_mon.observe(i[3:0]);
      static_only_mon.observe(i[3:0]);
    end

    for (i = 0; i < 8; ++i) begin
      branch_a.observe(i[2:0]);
      branch_b.observe(i[2:0]);
    end

    copy_src.observe(4'h1);
    copy_dst = new copy_src;
    `checkd(copy_dst.copy_cg == null, 1);
    global_dst = new global_src;
    `checkd(global_dst.cg == global_src.cg, 1);
    clone_dst = new clone_src;
    clone_base_view = clone_dst;
    `checkd(clone_dst.cg == null, 1);
    `checkd(clone_base_view.cg == null, 1);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
