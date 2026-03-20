// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  logic [500:0] x = 0;

  initial begin
    #1;
    x = 487274592023809;
    #5;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
