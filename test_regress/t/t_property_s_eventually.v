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

  localparam MAX = 4;
  integer cyc = 1;

  assert property (@(negedge clk) disable iff (cyc < MAX - 1) s_eventually (cyc == MAX - 1)) `PROPERTY_CHECK("s_eventually before final")

  assert property (@(negedge clk) disable iff (cyc < MAX - 1) s_eventually (cyc == MAX)) `PROPERTY_CHECK("s_eventually during final")

  assert property (@(negedge clk) disable iff (cyc < MAX - 1) s_eventually (cyc == MAX + 1)) `PROPERTY_CHECK("s_eventually after final")

  always @(posedge clk) begin
    ++cyc;
    if (cyc == MAX) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
