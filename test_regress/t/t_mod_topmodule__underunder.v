// DESCRIPTION: Verilator: Verilog Test module
//
// This test verifies that a top-module can be specified which
// is instantiated beneath another module in the compiled source
// code.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t_mod_topmodule__underunder;
  initial $finish;
endmodule

module faketop;
endmodule
