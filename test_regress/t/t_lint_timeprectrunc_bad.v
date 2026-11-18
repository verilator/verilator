// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  timeunit 1ns;
  timeprecision 10ps;

  initial begin
    #(500 * 1ps);
    #1ps;
    #0.015ns;
    #(0.5ns);
    #20ps;
    #0;
    #(1.01us);
    $finish;
  end
endmodule
