// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

module leaf(input logic clk);
  import "DPI-C" function void record_worker();
  always @(posedge clk) record_worker();
endmodule

module t(input logic clk);
  leaf u(.clk(clk));
endmodule
