// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jonathan Drolet
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  logic c /* verilator forceable */;

  initial begin
    assign c = 1'b1;
    #1 deassign c;
    #1;
    c <= 1'b0;
    #1;
    `checkh(c, 1'b0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
