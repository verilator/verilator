// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  localparam string AB = "AB";

  bit r;

  initial begin
    if (('bxz10 ==? 'bxxx0) !== 1) $stop;
    if (('bxz10 ==? 'bxxx1) !== 0) $stop;
    if (('bxz10 ==? 'bx1xx) !== 'x) $stop;
    if (('bxz10 !=? 'bxxx1) !== 1) $stop;
    if (('bxz10 !=? 'bxxx0) !== 0) $stop;
    if (('bxz10 !=? 'b1xx0) !== 'x) $stop;

    r = (AB ==? "AA");
    `checkd(r, 0);
    r = (AB ==? "AB");
    `checkd(r, 1);
    r = (AB !=? "AB");
    `checkd(r, 0);

    // real/shortreal is illegal so not tested here

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
