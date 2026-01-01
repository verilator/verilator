// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Verilator lint_off COVERIGN

module t;

  covergroup cg_opt;
    type_option.weight = 1;  // ok
    option.name = "the_name";  // pk
    bad_cg_non_option.name = "xx";  // <--- Bad
  endgroup

  covergroup cg_cross3;
    cross a, b{
      option.comment = "cross";  // ok
      bad_cross_non_option.name = "xx";  // <--- Bad
    }
  endgroup

  initial $stop;
endmodule
