// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Eduardo Schwarz Danni
// SPDX-License-Identifier: CC0-1.0

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  initial begin
    @(posedge clk);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
