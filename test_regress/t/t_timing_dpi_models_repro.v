// DESCRIPTION: Verilator: Evaluate two models on the same DPI call stack
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module a;
  import "DPI-C" function int step_b();
  initial begin
    int result;
    result = step_b();
    `checkd(result, 1);
    $display("*-* All Finished *-*");
  end
endmodule

module b;
  import "DPI-C" context task b_imp();
  export "DPI-C" task b_ex;
  int v = 0;
  task b_ex();
    v = 7;
  endtask
  initial begin
    b_imp();
    `checkd(v, 7);
  end
endmodule
