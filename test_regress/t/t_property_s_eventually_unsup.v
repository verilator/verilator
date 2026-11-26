// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk = 0;
  initial forever #1 clk = ~clk;

  localparam MAX = 3;
  integer cyc = 1;

  assert property (@(posedge clk) s_eventually ##1 1);
  assert property (@(negedge clk) s_eventually ##1 1);

  // s_eventually as an operand of a property operator
  assert property (@(posedge clk) cyc[0] or s_eventually cyc[1]);

  assert property (@(posedge clk) s_eventually s_eventually cyc[0]);

  // s_eventually alongside an unsupported sequence operator
  assert property (@(posedge clk) cyc[0] [= 2] |-> s_eventually cyc[1]);

  always @(posedge clk) begin
    ++cyc;
    if (cyc == MAX) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
