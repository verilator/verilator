// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  initial begin
    int a[5];
    int b[4];
    int one[1];
    int d[];
    int de[];  // Empty
    int q[$];
    int qe[$];  // Empty
    int res[];

    // Fixed unpacked array
    a = '{1, 2, 3, 4, 5};
    res = a.map() with (item * 2);
    `checkh(res.size, 5);
    `checkh(res[0], 2);
    `checkh(res[1], 4);
    `checkh(res[2], 6);
    `checkh(res[3], 8);
    `checkh(res[4], 10);

    // Replace each element with its index
    res = a.map() with (item.index);
    `checkh(res.size, 5);
    `checkh(res[0], 0);
    `checkh(res[2], 2);
    `checkh(res[4], 4);

    // Named iterator: value + index
    res = a.map(x) with (x + x.index);
    `checkh(res[0], 1);  // 1 + 0
    `checkh(res[1], 3);  // 2 + 1
    `checkh(res[2], 5);  // 3 + 2
    `checkh(res[3], 7);  // 4 + 3
    `checkh(res[4], 9);  // 5 + 4

    // Boolean predicate
    res = a.map() with (item > 3);
    `checkh(res[0], 0);
    `checkh(res[1], 0);
    `checkh(res[2], 0);
    `checkh(res[3], 1);
    `checkh(res[4], 1);

    // Dynamic array
    d = '{10, 20, 30, 40};
    res = d.map() with (item / 10);
    `checkh(res.size, 4);
    `checkh(res[0], 1);
    `checkh(res[1], 2);
    `checkh(res[2], 3);
    `checkh(res[3], 4);

    // Map then sort
    d = '{5, 3, 8, 1, 7};
    res = d.map() with (item * item);
    res.sort;
    `checkh(res.size, 5);
    `checkh(res[0], 1);   // 1^2
    `checkh(res[1], 9);   // 3^2
    `checkh(res[2], 25);  // 5^2
    `checkh(res[3], 49);  // 7^2
    `checkh(res[4], 64);  // 8^2

    // Map result fed into sum
    d = '{1, 2, 3, 4};
    res = d.map() with (item + 1);
    `checkh(res.sum, 14);

    // Queue source
    q = '{10, 20, 30};
    res = q.map() with (item + item.index);
    `checkh(res.size, 3);
    `checkh(res[0], 10);  // 10 + 0
    `checkh(res[1], 21);  // 20 + 1
    `checkh(res[2], 32);  // 30 + 2

    // Single-element array
    one = '{99};
    res = one.map() with (item - 1);
    `checkh(res.size, 1);
    `checkh(res[0], 98);

    // Empty arrays
    res = de.map() with (item * 2);
    `checkh(res.size, 0);
    res = qe.map() with (item + 1);
    `checkh(res.size, 0);

    // Index-only expression
    b = '{100, 200, 300, 400};
    res = b.map() with (item.index * 10);
    `checkh(res[0], 0);
    `checkh(res[1], 10);
    `checkh(res[2], 20);
    `checkh(res[3], 30);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
