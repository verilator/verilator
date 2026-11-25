// DESCRIPTION: Verilator: Rise/fall delays scaled by the module time unit
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x (%s !== %s)\n", `__FILE__, `__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0)
`define check_all(exp) do begin `checkh(out_assign, exp); `checkh(out_buf, exp); `checkh(out_net, exp); end while(0)
// verilog_format: on

`timescale 1ns / 1ps

module t;
  logic in = 1'b0;
  wire out_assign;
  wire out_buf;
  wire #(1.5, 2) out_net;

  assign #(1.5, 2) out_assign = in;
  buf #(1.5, 2) u_buf (out_buf, in);
  assign out_net = in;

  initial begin
    #10;
    `check_all(1'b0);
    in = 1'b1;
    #1.4;
    `check_all(1'b0);
    #0.2;
    `check_all(1'b1);
    in = 1'b0;
    #1.9;
    `check_all(1'b1);
    #0.2;
    `check_all(1'b0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
