// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

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
    if ($c("helper()") != 42) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
