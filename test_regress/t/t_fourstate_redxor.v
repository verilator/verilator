// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    if (^integer'(0) !== 0) $stop;
    if (^integer'(1) !== 1) $stop;
    if (^integer'('x) !== 'x) $stop;
    if (^integer'('z) !== 'x) $stop;
    if (^integer'('b0000z0000) !== 'x) $stop;
    if (^integer'('b0000x0000) !== 'x) $stop;
    if (^integer'('b0000z0010) !== 'x) $stop;
    if (^integer'('b0000x0100) !== 'x) $stop;
    if (^integer'('b0000z0011) !== 'x) $stop;
    if (^integer'('b0000x0101) !== 'x) $stop;
    if (^integer'('b000000011) !== 0) $stop;
    if (^integer'('b000000101) !== 0) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
