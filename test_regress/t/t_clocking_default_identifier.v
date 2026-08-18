// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  int cyc = 0;

  always @(negedge clk) begin  // negedge so there is nothing after $finish
    cyc <= cyc + 1;
    if (cyc == 12) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  clocking cb @(posedge clk);
  endclocking

  default clocking cb;
  initial begin
    ##2;
    if ($time != 20) $stop;
    ##5;
    if ($time != 70) $stop;
    ##3;
    if ($time != 100) $stop;
  end
endmodule
