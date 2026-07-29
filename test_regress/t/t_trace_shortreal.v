// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;

  bit clk;
  shortreal scalar = 1.25;
  shortreal arr[2];

  always #10 clk = ~clk;

  initial begin
    arr[0] = shortreal'(0.5);
    arr[1] = shortreal'(-2.25);

    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars(0, top);

    @(posedge clk);
    scalar = shortreal'(1.5);
    arr[0] = shortreal'(3.25);

    @(posedge clk);
    arr[1] = shortreal'(-4.5);

    @(posedge clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
