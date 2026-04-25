// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkb(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='b%x exp='b%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  reg [1:0] a=0, b=1;
  reg [1:0] r;
  initial begin
    r = 2'b00;
    #1; assign r = 2'b01;
    `checkb(r, 2'b01)
    #1; r = 2'b00; // ignored
    `checkb(r, 2'b01)
    #1; deassign r;
    `checkb(r, 2'b01)
    #1; r = 2'b00;
    `checkb(r, 2'b00)
    #1; assign r = a;
    `checkb(r, 2'b00)
    #1; a = 2'b01;
    `checkb(r, 2'b01)
    #1; a = 2'b00;
    `checkb(r, 2'b00)
    #1; force r = a + b;
    #1; a = 2'b00; b = 2'b00;
    `checkb(r, 2'b00)
    #1; a = 2'b01; b = 2'b01;
    `checkb(r, 2'b10)
    #1; assign r = b; // covered
    #1; r = 2'b11; // ignored
    `checkb(r, 2'b10)
    #1; release r;
    `checkb(r, 2'b01)
    #1; b = 2'b00;
    `checkb(r, 2'b00)
    $finish;
  end
endmodule
