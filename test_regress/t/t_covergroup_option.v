// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test option.name syntax: both declaration-time and runtime assignment compile.
// Note: option.name does not currently affect the coverage.dat hierarchy key;
// the type name is used regardless.

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
