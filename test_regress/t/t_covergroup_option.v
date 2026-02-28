// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  // verilator lint_off COVERIGN
  covergroup cg();
    option.name = "decl_name";
  endgroup

  cg cov1;

  initial begin
    cov1 = new;
    cov1.option.name = "new_cov1_name";
    $finish;
  end

endmodule
