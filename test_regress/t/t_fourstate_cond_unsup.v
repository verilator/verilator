// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    if ('x ? 1 : 0) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
