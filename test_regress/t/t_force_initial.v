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
  reg [1:0] a = 0;
  reg [1:0] b = 2;

  initial begin
     force b = a;
     `checkh(a, 0);
     `checkh(b, 0);
  end

  initial begin
    #1;
    `checkh(b, 0);

    a = 1;
    #1;
    `checkh(a, 1);
    `checkh(b, 1);

    a = 3;
    #1;
    `checkh(a, 3);
    `checkh(b, 3);

    release b;
    `checkh(a, 3);
    `checkh(b, 3);

    b = 0;
    #1;
    `checkh(b, 0);

    #1 $finish;
  end

endmodule
