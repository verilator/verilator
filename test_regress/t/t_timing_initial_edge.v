// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    #10;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
