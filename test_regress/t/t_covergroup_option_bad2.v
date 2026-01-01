// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Verilator lint_off COVERIGN

module t;
  // verilator lint_off COVERIGN
  covergroup cg();
  endgroup

  cg cov1;

  initial begin
    cov1 = new;
    cov1.not_an_option.name = "new_cov1_name";  // <--- Bad
    $finish;
  end

endmodule
