// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    if (1 / $c(0) !== 'x) $stop;
    if ($c(1) / $c(0) !== 'x) $stop;
    if ($c(1) / 0 !== 'x) $stop;
    if (1 / 0 !== 'x) $stop;
    if (6 / 3 !== 2) $stop;
    if ($c(6) / 3 !== 2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
