// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  sequence s;
    bit x;
    (1,
    x = 1
    );
  endsequence
  assert property (@(posedge clk) s);
endmodule
