// DESCRIPTION: Verilator: Names of instances in a library
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  lib u_lib ();
endmodule

`ifndef USE_LIB
module lib;
  /*verilator hier_block*/
  sub u0 ();
  sub u1 ();
endmodule

module sub;
  initial $display("In '%m'");
endmodule
`endif
