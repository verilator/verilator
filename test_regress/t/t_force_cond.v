// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

`define IMPURE_ONE |($random | $random)

module t;
  reg [1:0] a = 2;
  bit [1:0] b = 1;
  bit [1:0] c = 0;

  initial begin
    force a = b;
    if (`IMPURE_ONE == 1) force a = c;
    if (`IMPURE_ONE == 0) force a = b;
    c = 3;
    b = 2;
    #1;
    `checkh(a, 3);
    if (`IMPURE_ONE == 1) force a = b;
    if (`IMPURE_ONE == 0) force a = c;
    c = 2;
    b = 1;
    #1;
    `checkh(a, 1);
    #1 $finish;
  end

endmodule
