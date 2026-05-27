// DESCRIPTION: Verilator: Verilog example module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// See also https://verilator.org/guide/latest/examples.html"

// Found on Stackoverflow
int stdout_fd = 32'h8000_0001;
int stderr_fd = 32'h8000_0002;

module top;
  initial begin
    // display
    $display("Hello World!");
    $system("echo In a shell now");
    $display("Hello 3rd rock!");
    // fdisplay with stdout and stderr
    $fdisplay(stdout_fd, "Hello Mars!");
    $system("echo In another shell now");
    $fdisplay(stderr_fd, "Hello Pluto!");
    $finish;
  end
endmodule
