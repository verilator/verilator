// DESCRIPTION: Verilator: R3 reproducer, evaluate two models on the same DPI call stack
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module a;
  import "DPI-C" function int step_b();
  initial $display("a: step_b returned %0d", step_b());
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
    $display("b: v=%0d", v);
  end
endmodule
