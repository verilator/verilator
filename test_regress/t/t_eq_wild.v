// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    if (('bxz10 ==? 'bxxx0) !== 1) $stop;
    if (('bxz10 ==? 'bxxx1) !== 0) $stop;
    if (('bxz10 ==? 'bx1xx) !== 'x) $stop;
    if (('bxz10 !=? 'bxxx1) !== 1) $stop;
    if (('bxz10 !=? 'bxxx0) !== 0) $stop;
    if (('bxz10 !=? 'b1xx0) !== 'x) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
