// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  initial begin
    automatic int tofind;
    automatic int aliases[$];
    automatic int found[$];
    automatic int i;
    automatic byte byteq[$] = {2, -1, 127};
    automatic byte b[];
    automatic logic [7:0] m[2][2];
    automatic logic bit_arr[1024];

    aliases = '{1, 4, 6, 8};
    tofind = 6;
    found = aliases.find with (item == 1);
    `checkh(found.size, 1);
    found = aliases.find(j) with (j == tofind);
    `checkh(found.size, 1);
    // And as function
    aliases.find(i) with (i == tofind);

    // No parenthesis
    tofind = 0;
    found = aliases.find with (item == tofind);
    `checkh(found.size, 0);
    aliases.find with (item == tofind);

    // bug3387
    i = aliases.sum();
    `checkh(i, 'h13);
    i = byteq.sum() with (int'(item));
    `checkh(i, 128);

    // Unique (array method)
    tofind = 4;
    found = aliases.find with (tofind);  // "true" match
    `checkh(found.size, 4);
    found = aliases.find() with (item == tofind);
    `checkh(found.size, 1);
    found = aliases.find(i) with (i == tofind);
    `checkh(found.size, 1);
    i = aliases.or(v) with (v);
    `checkh(i, 'hf);
    i = aliases.and(v) with (v);
    `checkh(i, 0);
    i = aliases.xor(v) with (v);
    `checkh(i, 'hb);

    // Based roughly on IEEE 1800-2023 7.12.3
    // verilator lint_off WIDTHEXPAND
    b = {1, 2, 3, 4};
    i = b.sum;  // = 10 <= 1 + 2 + 3 + 4
    `checkd(i, 10);

    i = b.product;  // = 24 <= 1 * 2 * 3 * 4
    `checkd(i, 24);

    i = b.xor with (item + 4);  // = 12 <= 5 ^ 6 ^ 7 ^ 8
    `checkd(i, 12);

    m = '{'{5, 10}, '{15, 20}};
    i = m.sum with (item.sum with (item));  // = 50 <= 5+10+15+20
    `checkd(i, 50);

    // Width of the reduction method's result is the dtype of the with's expression
    // verilator lint_on WIDTHEXPAND
    for (i = 0; i < 1024; ++i) bit_arr[i] = 1'b1;
    i = bit_arr.sum with (int'(item));  // forces result to be 32-bit
    `checkd(i, 1024);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
