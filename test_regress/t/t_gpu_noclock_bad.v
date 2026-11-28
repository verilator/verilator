// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Eduardo Schwarz Danni
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  int cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 9) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
