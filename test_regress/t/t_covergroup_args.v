// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

// A plain (non-covergroup) class - exercises the non-covergroup class scope/varscope paths
class PlainClass;
    int x;
endclass

// Top-level (file-scope) covergroup: exercises the m_modp==null path in
// V3LinkParse::visit(AstCovergroup*), line 1269 false branch (libname = "")
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
    cp1: coverpoint i;  // Non-empty body with args: exercises constructor-body path
  endgroup

  // Clocked covergroup with constructor args: exercises the loop-past-sentinel path in
  // V3LinkParse createCovergroupMethods (iterates past AstCovergroup sentinel to find 'new')
  covergroup cg_clocked(int lim) @(posedge clk);
    cp_clocked: coverpoint i;
  endgroup

  cg cov1 = new(69, 77);
  cg cov2 = new(69);
  cg_clocked cov_clocked = new(10);
  PlainClass plain_inst = new;  // Non-covergroup class instance: exercises early-return paths

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

endmodule
