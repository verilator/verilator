// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Michael Bedford Taylor
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Release and deassign of a wide variable range in combinational logic
module t;
  logic [199:0] w;
  logic [199:0] a;
  logic en = 0;
  logic [7:0] v = 8'h5a;

  always @* begin
    if (en) force w[47:40] = v;
    else release w[47:40];
  end

  // verilator lint_off IEEEMAYDEPRECATE
  always @* begin
    if (en) assign a[47:40] = v;
    else deassign a[47:40];
  end
  // verilator lint_on IEEEMAYDEPRECATE

  initial begin
    w = '0;
    a = '0;
    #1 en = 1;
    #1 en = 0;
    #1;
    `checkh(w[47:40], 8'h5a);
    `checkh(a[47:40], 8'h5a);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
