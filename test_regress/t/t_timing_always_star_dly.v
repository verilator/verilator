// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`timescale 1ns / 1ps

module t;
  // Free-running clock from a self-inverting intra-assignment-delayed NBA in 'always @(*)'
  logic en = 1'b0;
  logic q = 1'b0;
  always @(*) if (en) q <= #5 ~q;

  int n = 0;
  time last = 0;
  always @(posedge q) begin
    if (n != 0) `checkd($time - last, 10);
    last = $time;
    ++n;
  end

  initial begin
    #10 en = 1'b1;
    #100;
    `checkd(n, 10);
    `checkd(last, 105);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
