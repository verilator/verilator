// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    if (|integer'(0) !== 0) $stop;
    if (|integer'(1) !== 1) $stop;
    if (|integer'('x) !== 'x) $stop;
    if (|integer'('z) !== 'x) $stop;
    if (|integer'('b0000z0000) !== 'x) $stop;
    if (|integer'('b0000x0000) !== 'x) $stop;
    if (|integer'('b0000z0010) !== 1) $stop;
    if (|integer'('b0000x0100) !== 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
