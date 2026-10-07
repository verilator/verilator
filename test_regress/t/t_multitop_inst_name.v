// DESCRIPTION: Verilator: Names of instances under multiple top modules
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off MULTITOP

`ifndef USE_LIB
module sub;
  initial $display("In '%m'");
endmodule
`endif

module top_a;
  sub u0 ();
  sub u1 ();
endmodule

module top_bb;
  sub u0 ();
  sub u1 ();
endmodule
