// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test option.name syntax: both declaration-time and runtime assignment compile.
// Note: option.name does not currently affect the coverage.dat hierarchy key;
// the type name is used regardless.
// Also tests option.weight, option.goal, option.per_instance, option.comment.

module t;
  // verilator lint_off COVERIGN
  logic [3:0] data;

  covergroup cg();
    option.name = "decl_name";
  endgroup

  // Test option.weight, option.goal, option.per_instance, option.comment
  // Covergroup-level options (parsed but passed through constructor body)
  covergroup cg2;
    option.weight      = 2;
    option.goal        = 90;
    option.per_instance = 1;
    option.comment     = "my covergroup";
    cp: coverpoint data;
  endgroup

  // Coverpoint-level options: weight, goal, per_instance, and comment
  covergroup cg3;
    cp: coverpoint data {
      option.weight      = 2;
      option.goal        = 90;
      option.per_instance = 1;
      option.comment     = "cp comment";
      bins lo = {[0:7]};
      bins hi = {[8:15]};
    }
  endgroup

  cg  cov1;
  cg2 cov2;
  cg3 cov3;

  initial begin
    cov1 = new;
    cov1.option.name = "new_cov1_name";

    cov2 = new;
    data = 5;
    cov2.sample();

    cov3 = new;
    data = 3;
    cov3.sample();
    data = 10;
    cov3.sample();

    $finish;
  end

endmodule
