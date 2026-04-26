// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk = 0;
  int cyc = 0;

  initial forever #1 clk = ~clk;

  always @(posedge clk) begin
    cyc = cyc + 1;
    if (cyc >= 10) $finish;
  end

  always @(posedge clk) begin
    fork
      begin
        while ($sampled(cyc) != 99) #1;
        if (cyc >= 10) $stop;
      end
    join_none
  end
endmodule
