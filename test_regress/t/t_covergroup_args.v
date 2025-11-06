// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off COVERIGN
module t;

  covergroup cg(int var1, int var2 = 42);
  endgroup

  cg cov1 = new(69, 77);
  cg cov2 = new(69);

  int i, j;
  real r;

  function void x();
    cov1.set_inst_name("the_inst_name");
    cov1.start();
    cov1.sample();
    cov1.stop();

    void'(cov2.get_coverage());
    r = cov2.get_coverage();
    r = cov2.get_coverage(i, j);
    // verilator lint_off IGNOREDRETURN
    cov2.get_inst_coverage();
    // verilator lint_on IGNOREDRETURN
    r = cov2.get_inst_coverage(i, j);

    cg::get_coverage();
    r = cg::get_coverage();
    r = cg::get_coverage(i, j);
  endfunction

endmodule
