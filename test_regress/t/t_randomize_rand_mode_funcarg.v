// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test: rand_mode() used as a function argument (not standalone expression)
// Ensures nested rand_mode() calls inside function arguments are properly
// transformed and do not cause Internal Error in V3SplitVar.

class RandModeClass;
  rand int x;
  rand int y;

  constraint c { x inside {[1:255]}; y inside {[1:255]}; }

  task check_mode(string name, int actual, int expected);
    if (actual !== expected) begin
      $display("Error: %s.rand_mode() = %0d, expected %0d", name, actual, expected);
      $stop;
    end
  endtask

  // Task that calls check_mode with rand_mode() as argument
  task test_funcarg;
    check_mode("x", x.rand_mode(), 1);
    check_mode("y", y.rand_mode(), 1);

    x.rand_mode(0);
    check_mode("x", x.rand_mode(), 0);
    check_mode("y", y.rand_mode(), 1);

    x.rand_mode(1);
    check_mode("x", x.rand_mode(), 1);

    // Also test using rand_mode() in $display arguments
    $display("x.rand_mode=%0d y.rand_mode=%0d", x.rand_mode(), y.rand_mode());
  endtask
endclass

module t;
  initial begin
    automatic RandModeClass obj = new;
    obj.test_funcarg();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
