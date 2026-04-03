// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  int a;
  int b;
  int i;
  int arr[5];

  // function with side effects
  function int foo();
    $display("foo");
    return 1;
  endfunction;

  // verilator lint_off ASSIGNEQEXPR
  initial begin
    a = 10;
    i = (a = 2);
    `checkd(a, 2);
    `checkd(i, 2);

    a = 10;
    i = (a += 2);
    `checkd(a, 12);
    `checkd(i, 12);

    a = 10;
    i = (a -= 2);
    `checkd(a, 8);
    `checkd(i, 8);

    a = 10;
    i = (a *= 2);
    `checkd(a, 20);
    `checkd(i, 20);

    a = 10;
    i = (a /= 2);
    `checkd(a, 5);
    `checkd(i, 5);

    a = 11;
    i = (a %= 2);
    `checkd(a, 1);
    `checkd(i, 1);

    a = 10;
    i = (a &= 2);
    `checkd(a, 2);
    `checkd(i, 2);

    a = 8;
    i = (a |= 2);
    `checkd(a, 10);
    `checkd(i, 10);

    a = 10;
    i = (a ^= 2);
    `checkd(a, 8);
    `checkd(i, 8);

    a = 10;
    i = (a <<= 2);
    `checkd(a, 40);
    `checkd(i, 40);

    a = 10;
    i = (a >>= 2);
    `checkd(a, 2);
    `checkd(i, 2);

    a = 10;
    i = (a >>>= 2);
    `checkd(a, 2);
    `checkd(i, 2);

    a = 10;
    i = (a = (b = 5));
    `checkd(a, 5);
    `checkd(i, 5);
    `checkd(b, 5);

    a = 10;
    b = 6;
    i = ((a += (b += 1) + 1));
    `checkd(a, 18);
    `checkd(i, 18);
    `checkd(b, 7);

    arr[0] = 3;
    arr[0] += 4;
    `checkd(arr[0], 7);

    arr[foo()] = 1;
    arr[foo()] += 2;
    `checkd(arr[1], 3);

    arr[foo() + 1] = 6;
    arr[foo() + 1] -= 5;
    `checkd(arr[2], 1);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
