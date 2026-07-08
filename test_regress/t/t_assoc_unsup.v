// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    bit[229:0] qw[int]; // Wide values
    bit[229:0] qwe[int]; // Wide values - empty
    bit[229:0] qwv[$];  // Wide values - Value returns
    int qi[$];  // Index returns
    bit[229:0] w;

    qw = '{10: 1, 11: 2, 12: 2, 13: 4, 14: 3};

    qwv = qwe.min(x) with (x + 1);
    qwv = qwe.max(x) with (x + 1);

    w = qw.sum with (item + 1);
    w = qw.product with (item + 1);

    w = qwe.sum with (item + 1);
    w = qwe.product with (item + 1);

    qw = '{10: 230'b1100, 11: 230'b1010};
    w = qw.and with (item + 1);
    w = qw.or with (item + 1);
    w = qw.xor with (item + 1);

    w = qw.and() with (item + 1);
    w = qw.or() with (item + 1);
    w = qw.xor() with (item + 1);

    qwv = qw.find with (item == 2);
    qwv = qw.find_first with (item == 2);
    qwv = qw.find_last with (item == 2);

    qi = qw.find_index with (item == 2);
    qi = qw.find_first_index with (item == 2);
    qi = qw.find_last_index with (item == 2);

    // Map method (IEEE 1800-2023 7.12.5)
    qw = '{1: 100, 2: 200, 3: 300};
    qwv = qw.map(el) with (el / 100);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
