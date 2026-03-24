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

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
