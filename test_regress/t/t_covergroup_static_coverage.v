// DESCRIPTION: Verilator: Verilog Test module
//
// Tests: static/type-level get_coverage() with multiple instances,
// progressive coverage queries via get_inst_coverage(), and dynamic
// instance creation (including nested-scope instances).
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  // cg: three bins; used for multiple-instance and progressive-query tests
  covergroup cg;
    coverpoint data {
      bins low  = {[0:1]};
      bins mid  = {[2:3]};
      bins high = {[4:5]};
    }
  endgroup

  // cg2: two bins; used for dynamic (new) instance creation test
  covergroup cg2;
    coverpoint data {
      bins low  = {[0:1]};
      bins high = {[2:3]};
    }
  endgroup

  int data;

  initial begin
    // Declare all handles before any statements
    cg cg1, cg2_unused, cg3, cg_q;
    cg2 dyn_inst;

    // Multiple static instances: each samples a different bin
    cg1 = new;
    cg2_unused = new;
    cg3 = new;
    data = 0; cg1.sample();         // low
    data = 2; cg2_unused.sample();  // mid
    data = 4; cg3.sample();         // high

    // Progressive coverage query via get_inst_coverage()
    cg_q = new;
    data = 0; cg_q.sample();
    $display("After low:  %0.1f%%", cg_q.get_inst_coverage());
    data = 2; cg_q.sample();
    $display("After mid:  %0.1f%%", cg_q.get_inst_coverage());
    data = 4; cg_q.sample();
    $display("After high: %0.1f%%", cg_q.get_inst_coverage());

    // Dynamic instance creation (from t_covergroup_dynamic)
    dyn_inst = new;
    data = 0; dyn_inst.sample();  // low
    data = 2; dyn_inst.sample();  // high
    begin
      cg2 dyn2;
      dyn2 = new;
      data = 0; dyn2.sample();   // low
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
