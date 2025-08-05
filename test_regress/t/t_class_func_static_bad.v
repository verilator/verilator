// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  class C;
    task static task_st(int x);  // BAD - methods have automatic lifetime
      int y;
      y = 2 * x;
    endtask
    function static int func_st(int x);  // BAD - methods have automatic lifetime
      int y;
      y = 2 * x;
      return y;
    endfunction
  endclass

  initial $stop;

endmodule
