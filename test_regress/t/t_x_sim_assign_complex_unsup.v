// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  logic [10:0] x;
  assign #1{x[10:9], x[5:0]} = x[7:0];
  initial begin
    #1;
    $write("%d\n", x);
    $finish;
  end
endmodule
