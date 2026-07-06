// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t(input clk);
  int cyc;

  default disable iff (cyc < 3);

  generate
    begin : g
      default disable iff (cyc < 5);
      default disable iff (cyc < 7);

      assert property (@(posedge clk) 0);
    end
  endgenerate
endmodule
