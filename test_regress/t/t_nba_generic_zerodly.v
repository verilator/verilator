// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkt(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0t exp=%0t (%t !== %t)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  // An NBA made after resuming from a '#0' is committed in the same time slot
  int x = 2;
  always begin
    `checkh(x, 2);
    #0;
    `checkh(x, 2);
    x <= 4;
    `checkh(x, 2);
    #1;
    `checkh(x, 4);
    $write("*-* All Finished *-*\n");
    $finish;
  end
  initial begin
    `checkh(x, 2);
    @(x);
    `checkt($time, 0);
    `checkh(x, 4);
  end

  // A blocking write made after resuming from a '#0' is kept, when committing an NBA of clocked
  // logic made before it in the same time slot
  logic clk = 0;
  int y = 0;
  always @(posedge clk) y[0] <= 1'b0;
  initial begin
    #0;  // Let the process above start waiting for the edge
    clk = 1;
    #0;
    y = 5;
  end
  final `checkh(y, 4);
endmodule
