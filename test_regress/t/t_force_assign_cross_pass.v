// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jonathan Drolet
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define IMPURE_ONE |($random | $random)
// verilog_format: on

module t;
  logic [7:0] a /* verilator forceable */;
  assign a = 8'hA5;

  logic b;

  initial begin
    if (`IMPURE_ONE == 0) force a = 8'h00;
    else release a;

    assign b = 1'b1;

    `checkh(a, 8'hA5);
    `checkh(b, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
