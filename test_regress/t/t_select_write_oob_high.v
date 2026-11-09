// DESCRIPTION: Check that a blocking partial write with select outside of MSB
// of a 2-state vector doesn't corrup lvalue write refs.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: $time=%0t got='h%x exp='h%x\n", `__FILE__,`__LINE__, $time, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;

  initial begin
    bit [5:0] x;
    integer i;

    // verilator lint_off SELRANGE
    x = 'h0;
    x[8:4] = 5'b10001;
    `checkh(x, 6'b010000);  // Const, partially OOB high

    x = 'h0;
    x[11:6] = 6'b111111;
    `checkh(x, '0);  // Const, fully OOB high

    x = 'h0;
    x[9:3] = 7'b1011010;
    `checkh(x, 6'b010000);  // Const, select width > declared width, OOB high

    i = 4;
    x = 'h0;
    x[i+:5] = 5'b10001;
    `checkh(x, 6'b010000);  // Var, partially OOB high

    i = 6;
    x = 'h0;
    x[i+:6] = 6'b111111;
    `checkh(x, '0);  // Var, fully OOB high

    i = 3;
    x = 'h0;
    x[i+:7] = 7'b1011010;
    `checkh(x, 6'b010000);  // Var, select width > declared width, OOB high
    // verilator lint_on SELRANGE

    $write("*-* All finished *-*\n");
    $finish;
  end
endmodule
