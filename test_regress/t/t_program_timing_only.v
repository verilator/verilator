// DESCRIPTION: Verilator: Timing with only reactive processes
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  reactive_only p ();
endmodule

program reactive_only;
  bit [6:0] value;
  initial begin
    #1;
    `checkd(int'($time), 1)
    value <= 7'd9;
    #0;
    `checkd(value, 0)
    @(value);
    `checkd(value, 9)
    #1;
    `checkd(int'($time), 2)
    $write("*-* All Finished *-*\n");
    $finish;
  end
endprogram
