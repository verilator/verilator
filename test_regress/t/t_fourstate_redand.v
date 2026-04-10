// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    if (&integer'('b00000000000000000000000000000000) !== 0) $stop;
    if (&integer'('b00000000000000000000000000000100) !== 0) $stop;
    if (&integer'('b10000000000000000000000000010100) !== 0) $stop;
    if (&integer'('b0000000000000000000000000000000x) !== 0) $stop;
    if (&integer'('b00000000000000000000000000000z0x) !== 0) $stop;
    if (&integer'('b00000000000000000000000000000z00) !== 0) $stop;
    if (&integer'('b0xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx) !== 0) $stop;
    if (&integer'('b1xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx) !== 'x) $stop;
    if (&integer'('b1zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz) !== 'x) $stop;
    if (&integer'('b1zzzzzzzzzzzzzzzzzzzzzxxxxxxxxxx) !== 'x) $stop;
    if (&integer'('b1111111111111111111111111111111x) !== 'x) $stop;
    if (&integer'('b1111111111111111111111111111111z) !== 'x) $stop;
    if (&integer'('b11111111111111111111111111111111) !== 1) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
