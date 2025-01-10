// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  class Cls;
    local typedef bit t1;
    protected typedef bit t2;
  endclass

  Cls::t1 var1;  // BAD: access error expected
  Cls::t2 var2;  // BAD: access error expected

endmodule
