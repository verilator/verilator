// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define PROPERTY_CHECK(msg) \
    $display("[%0t] stmt, %s", $time, msg); \
  else \
    $display("[%0t] else, %s", $time, msg); \
// verilog_format: on

module t;
  bit clk = 0;
  initial forever #1 clk = ~clk;

  localparam MAX = 1000;
  integer cyc = 0;
  integer passed = 0;

  assert property (@(negedge clk) s_eventually 1)
    ++passed;

  always @(posedge clk) begin
    ++cyc;
    if (cyc == MAX) begin
      $display("%d", passed);
      if (passed != 999) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
