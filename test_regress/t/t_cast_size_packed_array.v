// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Denis Yusim
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); errors++; end while(0);
// verilog_format: on

// Size cast of a right-shifted multi-dimensional packed array.
// IEEE 1800-2023 6.24.1: a size cast returns the value an [n-1:0] variable holds after
// being assigned the expression, so the shift is evaluated at the operand's full width.
module t;
  logic [23:0][127:0] arr2d;  // 3072 bits, 128-bit elements
  logic [23:0][15:0] arr16;  // 384 bits, 16-bit elements
  logic [3071:0] flat;  // same bits as arr2d
  logic [7:0] v8;
  int errors = 0;

  initial begin
    for (int i = 0; i < 24; i++) begin
      arr2d[i] = {16{8'(i + 1)}};  // every byte of element i is i+1
      arr16[i] = {2{8'(i + 1)}};
    end
    flat = arr2d;

    // Fail: the result needs operand bits at or above max(cast width, element width)
    `checkh(8'(arr2d >> 128), 8'h02);
    `checkh(8'(arr2d >> 512), 8'h05);
    `checkh(16'(arr2d >> 1024), 16'h0909);
    `checkh(8'(arr16 >> 16), 8'h02);
    `checkh(256'(arr2d >> 128), {{16{8'h03}}, {16{8'h02}}});  // upper 128 bits lost

    // Pass: every operand bit used is below max(cast width, element width)
    `checkh(8'(arr2d >> 8), 8'h01);
    `checkh(16'(arr2d >> 112), 16'h0101);

    // Pass: the same value written other ways
    `checkh(8'(flat >> 512), 8'h05);  // flat vector
    `checkh(8'({arr2d} >> 512), 8'h05);  // operand flattened by a concatenation
    /* verilator lint_off WIDTHTRUNC */
    v8 = arr2d >> 512;  // plain assignment
    /* verilator lint_on WIDTHTRUNC */
    `checkh(v8, 8'h05);

    if (errors != 0) `stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
