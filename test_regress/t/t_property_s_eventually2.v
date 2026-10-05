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
  integer passed_until = 0;

  assert property (@(negedge clk) s_eventually 1)
    ++passed;

  // 'until' after 's_eventually' in the same module (#8614)
  assert property (@(negedge clk) cyc > 0 until cyc > 0)
    ++passed_until;

  always @(posedge clk) begin
    ++cyc;
    if (cyc == MAX) begin
      $display("%d", passed);
      if (passed != 999) $stop;
      if (passed_until != 999) $stop;  // Same as 'passed': each attempt passes on its first edge
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
