// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); end while(0)

function bit [1:0] get_arg (bit [1:0] x);
   return x;
endfunction

module t;
  bit [1:0] a;
  bit [1:0] b = 1;

  initial begin
    #1 a = 0;
    force b = get_arg(a);
    `checkh(a, 0);
    `checkh(b, 0);

    a = 1;
    #1;
    `checkh(a, 1);
    `checkh(b, 1);

    a = 2;
    #1;
    `checkh(a, 2);
    // TODO
    // IEEE 1800-2023 10.6
    // Assignment shall be reevaluated while the assign or force is in effect.
    `checkh(b, 2);

    a = 3;
    #1;
    `checkh(a, 3);
    `checkh(b, 3);

    release b;
    `checkh(a, 3);
    `checkh(b, 3);

    b = 2;
    `checkh(b, 2);

    #1 $finish;
  end

endmodule
