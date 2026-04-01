// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    static logic v = 'x;
    $write("%d\n", v);
    v = 'z;
    $write("%d\n", v);
    v = 0;
    $write("%d\n", v);
    v = 1;
    $write("%d\n", v);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
