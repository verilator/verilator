// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  bit clk;
  int a, b;

  always #10 clk = ~clk;

  initial begin
    $monitor("[%0t] a=%0d b=%0d", $time, a, b);
    #1;  // So not on clock edge
    #100;
    a = 10;
    #10;
    b = 20;
    #10;
    a = 11;
    #10;
    b = 22;
    #10;
    // Changes in both the active and NBA regions, displays once with the final values
    a = 12;
    a <= 13;
    #10;
    $monitoroff;
    #10;
    // Displays immediately, without a value change
    $monitoron;
    #10;
    // Displays when invoked, without a value change
    $monitor("[%0t] second b=%0d", $time, b);
    #10;
    // Nothing to monitor, displays only when invoked
    $monitor("[%0t] no args", $time);
    #10;
    $monitoroff;
    #10;
    // Displays immediately, also with nothing to monitor
    $monitoron;
    #100;
    #10;
    $monitoroff;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
