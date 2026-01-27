// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under The Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  timeunit 1ns; timeprecision 1ps;

  initial begin
    `checkd($timeunit, -9);
    `checkd($timeunit(), -9);
    `checkd($timeunit(t), -9);

    `checkd($timeprecision, -12);
    `checkd($timeprecision(), -12);
    `checkd($timeprecision(t), -12);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
