// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

// A plain (non-covergroup) class included to verify it does not interfere with covergroup handling
class PlainClass;
    int x;
endclass

// Top-level (file-scope) covergroup declared outside any module
// verilator lint_off COVERIGN
covergroup cg_toplevel;
  cp_tl: coverpoint 0;
endgroup
// verilator lint_on COVERIGN

// verilator lint_off COVERIGN
module t;

  int i, j;
  logic clk = 0;

  covergroup cg(int var1, int var2 = 42);
    cp1: coverpoint i { bins lo = {[0:4]}; bins hi = {[5:9]}; }
  endgroup

  // Clocked covergroup with constructor arguments
  covergroup cg_clocked(int lim) @(posedge clk);
    cp_clocked: coverpoint i { bins lo = {[0:4]}; bins hi = {[5:9]}; }
  endgroup

  cg cov1 = new(69, 77);
  cg cov2 = new(69);
  cg_clocked cov_clocked = new(10);
  PlainClass plain_inst = new;  // Non-covergroup class instance — must not affect covergroup coverage

  function void x();
    cov1.set_inst_name("the_inst_name");
    cov1.start();
    cov1.sample();
    cov1.stop();

    void'(cov2.get_coverage());
    void'(cov2.get_coverage(i, j));
    // verilator lint_off IGNOREDRETURN
    cov2.get_inst_coverage();
    // verilator lint_on IGNOREDRETURN
    void'(cov2.get_inst_coverage(i, j));

    void'(cg::get_coverage());
    void'(cg::get_coverage(i, j));
  endfunction

  initial begin
    i = 3;
    x();             // samples cov1 with i=3 -> lo bin hit
    clk = 1;         // posedge: samples cov_clocked with i=3 -> lo bin hit
    $finish;
  end

endmodule
