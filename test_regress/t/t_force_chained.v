// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); end while(0)

module t;
  reg [1:0] a;
  wire [1:0] b = 1;
  bit [1:0] c;

  initial begin
    #1 a = 0;
    force b = a;
    force c = b;
    `checkh(a, 0);
    `checkh(b, 0);
    `checkh(c, 0);

    a = 1;
    #1;
    `checkh(a, 1);
    `checkh(b, 1);
    // TODO implement inter-dependency resolution between force statements
    `checkh(c, 1);

    a = 2;
    #1;
    `checkh(a, 2);
    `checkh(b, 2);
    `checkh(c, 2);

    a = 3;
    c = 3;
    #1;
    `checkh(a, 3);
    `checkh(b, 3);
    `checkh(c, 3);

    release b;
    release c;
    `checkh(a, 3);
    `checkh(b, 1);
    `checkh(c, 3);

    #1 $finish;
  end

endmodule
