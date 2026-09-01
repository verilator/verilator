// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Marco Frank
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

// Issue #5132: an array slice used as a bare value (not the LHS/RHS of an
// assignment) hit an internal error.
module t;
  byte mem[8] = '{1, 2, 3, 4, 5, 6, 7, 8};
  byte dmem[7:0] = '{10, 20, 30, 40, 50, 60, 70, 80};
  byte sub[4];

  task automatic check_arg(byte a[4]);
    `checkh(a[0], 8'd1);
    `checkh(a[3], 8'd4);
  endtask

  initial begin
    $display("%p", mem[0:3]);

    `checkh(mem[2:5][2], 8'd3);
    `checkh(mem[2:5][5], 8'd6);

    `checkh(dmem[5:2][5], 8'd30);
    `checkh(dmem[5:2][2], 8'd60);

    check_arg(mem[0:3]);

    `checkh(mem[0:3][2], 8'd3);

    sub = mem[0:3];
    `checkh(sub[0], 8'd1);
    `checkh(sub[3], 8'd4);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
