// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); end while(0)

module t;
  logic [7:0] a = 1;
  logic [7:0] b = 2;
  logic [7:0] c = 3;
  logic [7:0] d = 4;
  logic [7:0] e = 5;

  initial begin
    force e = a + b + c + d;
    `checkh(e, 10);
    #1;
    a = 0;
    `checkh(e, 10);
    #1;
    // TODO support multiple VarRefs on RHS
    `checkh(e, 9);

    b = 0;
    `checkh(e, 9);
    #1;
    `checkh(e, 7);

    c = 0;
    `checkh(e, 7);
    #1;
    `checkh(e, 4);

    d = 0;
    `checkh(e, 4);
    #1;
    `checkh(e, 0);

    release e;
    // Not driven, change value after procedural assignment.
    `checkh(e, 0);
    e = 5;
    `checkh(e, 5);

    $finish;
  end
endmodule
