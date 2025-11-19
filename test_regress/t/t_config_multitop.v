// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off "MULTITOP"
module m1;
  initial $display("In '%m'");
endmodule

module m2;
  initial $display("In '%m'");
endmodule

config cfg1;
  design m1 m2;
endconfig : cfg1  // Test end label
// verilator lint_on "MULTITOP"

