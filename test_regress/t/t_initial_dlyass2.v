// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  reg clk = 1;
  reg [7:0] d = 0;
  reg [7:0] q = 0;

  // Clock generation
  always #0.5 clk = ~clk;

  // Input signal generation
  initial begin
    // verilator lint_off INITIALDLY
    d <= 0;
    repeat (5) @(posedge clk);
    d <= 1;
    @(posedge clk);
    d <= 2;
    @(posedge clk);
    d <= 3;
    @(posedge clk);
    d <= 4;
    @(posedge clk);
    d <= 0;
    repeat (5) @(posedge clk);
    $finish;
  end

  // Unit under test (flip-flop)
  always @(posedge clk) q <= d;

  always @(negedge clk) begin
    $display("[%0t] d=%x q=%x", $time, d, q);
    if (d == 1) `checkd(q, 0);
    if (d == 2) `checkd(q, 1);
    if (d == 3) `checkd(q, 2);
    if (d == 4) `checkd(q, 3);
  end

endmodule
