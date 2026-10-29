// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input bit clk,
    input bit a
);
  assert property (@(posedge clk) eventually[0: 2] a);
  always @(posedge clk) assert property (eventually[0: 2] a);
  assert property (@(posedge clk) eventually[0: 2] (a ##1 a));
  assert property (@(posedge clk) s_eventually (a ##1 a));
  assert property (@(posedge clk) eventually[64'h1_0000_0000: 64'h1_0000_0000] a);
  assert property (@(posedge clk) (eventually[0: 1] a) implies (eventually[0: 1] a))
    $display("PASSED");
  else $display("FAILED");
endmodule
