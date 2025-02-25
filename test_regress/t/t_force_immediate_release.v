// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t;

  reg [2:0] a = 3'b000;

  initial begin
    a = 3'b001;
    `checkh(a, 1);

    force a = 3'b010;
    `checkh(a, 2);

    a = 3'b011;
    `checkh(a, 2);

    release a;
    `checkh(a, 2);

    a = 3'b100;
    `checkh(a, 4);

    $finish;
  end

endmodule
