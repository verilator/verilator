// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test the methods and options of coverpoints and crosses but get_inst_coverage() without
// arguments (IEEE 1800-2023 19.8, 19.10)

module t;
  int a;
  int b;
  int covered;
  int total;
  real r;

  covergroup cg;
    cp_a: coverpoint a;
    cp_b: coverpoint b;
    x: cross cp_a, cp_b;
  endgroup

  cg cg_i = new;

  initial begin
    r = cg_i.cp_a.get_coverage();
    cg_i.cp_a.start();
    cg_i.x.stop();
    cg_i.cp_b.option.weight = 2;
    $display("%0d", cg_i.x.type_option.weight);
    r = cg_i.x.get_inst_coverage(covered, total);
  end
endmodule
