// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); end while(0)

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
    // TODO trigger forced variable update from different initial block.
    `checkh(b, 1);

    a = 2;
    #1;
    `checkh(a, 2);
    `checkh(b, 2);

    release b;
    `checkh(a, 2);
    `checkh(b, 2);

    b = 0;
    #1;
    `checkh(b, 0);

    #1 $finish;
  end

endmodule
