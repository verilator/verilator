// DESCRIPTION: Verilator: %m in a module with several instances, whose code is combined
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  lib u_lib ();
endmodule

`ifndef USE_LIB
module lib;
  sub u0 ();
  sub u1 ();
  sub u2 ();
endmodule

module sub;
  /* verilator no_inline_module */
  task automatic tsk;
    $display("In '%m'");
  endtask
  initial begin
    $display("In '%m'");
    begin : blk
      $display("In '%m'");
    end
    tsk();
  end
endmodule
`endif
