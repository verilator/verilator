// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface class I;
`systemc_header
int helper();
`systemc_imp_header
#define NUM 42
`systemc_implementation
int helper() { return NUM; }
`verilog
endclass

module t;
  initial begin
    `checkd($c("helper()"), 42);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
