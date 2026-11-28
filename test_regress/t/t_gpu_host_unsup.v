// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Eduardo Schwarz Danni
// SPDX-License-Identifier: CC0-1.0

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if ($test$plusargs("stop_early") || cyc == 9) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
