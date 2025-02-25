// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t;
  reg [1:0] a;
  wire [1:0] b = 1;

  initial begin
    #1 a = 0;
    force b = a;
    `checkh(a, 0);
    `checkh(b, 0);

    #1 a = 1;
    `checkh(a, 1);
    `checkh(b, 0);

    #1 a = 2;
    `checkh(a, 2);
    `checkh(b, 1);

    #1 a = 3;
    `checkh(a, 3);
    `checkh(b, 2);

    #1 release b;
    `checkh(a, 3);
    `checkh(b, 1);

    #1 $finish;
  end

endmodule
