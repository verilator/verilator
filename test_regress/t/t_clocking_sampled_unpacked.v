// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nikolai Kumar
// SPDX-License-Identifier: CC0-1.0

module t;
  logic clk = 0;
  logic [1:0] data[1:0];
  logic [1:0] snap[1:0];

  clocking cb @(posedge clk);
    input data;
  endclocking

  always @(cb) snap <= cb.data;

  always #5 clk = ~clk;

  initial begin
    data[0] = 2'd1;
    data[1] = 2'd2;
    @(posedge clk);
    @(posedge clk);
    if (snap[0] !== 2'd1 || snap[1] !==2'd2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
