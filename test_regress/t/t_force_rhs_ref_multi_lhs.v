// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  bit [1:0] a;
  bit [1:0] b;

  bit [1:0] d;

  initial begin
    a = 0;
    force b = a;
    force d = a;
    a = 2;
    #1;
    `checkh(a, 2);
    `checkh(b, 2);
    `checkh(d, 2);
    a = 3;
    #1;
    `checkh(a, 3);
    `checkh(b, 3);
    `checkh(d, 3);
    #1 $finish;
  end

endmodule
