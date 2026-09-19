// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    static bit   foo;
    static logic bar;

    if (bar !== 'x) $stop;
    while (!bar) $stop;
    while (bar) $stop;
    while (bar) $stop;
    while (!foo) foo++;
    while (!bar) bar++;
    while (!foo) $stop;
    while (!bar) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
