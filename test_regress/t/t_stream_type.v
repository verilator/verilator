// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  initial begin
    bit b;
    automatic reg [2:0] foo0 [1:0] = '{0, 0};
    automatic reg [2:0] foo2 [1:0] = '{0, 2};
    automatic reg [2:0] foo4 [1:0] = '{1, 0};

    b = |type(logic [$bits(foo0)-1:0])'({>>{foo0}});
    $display("foo0 %p -> %b", foo0, b);
    `checkh(b, 1'b0);

    b = |type(logic [$bits(foo2)-1:0])'({>>{foo2}});
    $display("foo0 %p -> %b", foo2, b);
    `checkh(b, 1'b1);

    b = |type(logic [$bits(foo4)-1:0])'({>>{foo4}});
    $display("foo0 %p -> %b", foo4, b);
    `checkh(b, 1'b1);

    $finish;
  end
endmodule
