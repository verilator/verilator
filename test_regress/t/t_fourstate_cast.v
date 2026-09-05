// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    static int n = 12;
    static integer m = 'x;
    static int v = 1 + int'(1 + (n + m));
    if (v != 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
