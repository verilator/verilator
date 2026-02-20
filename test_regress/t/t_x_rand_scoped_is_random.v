// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2016 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t ();
  reg a0 = 'x;
  reg a1 = 'x;
  reg a2 = 'x;
  reg a3 = 'x;
  reg a4 = 'x;
  reg a5 = 'x;
  reg a6 = 'x;
  reg a7 = 'x;
  reg a8 = 'x;
  reg a9 = 'x;
  reg a10 = 'x;
  reg a11 = 'x;
  reg a12 = 'x;
  reg a13 = 'x;
  reg a14 = 'x;
  reg a15 = 'x;

  integer fd;
  initial begin
    fd = $fopen({`STRINGIFY(`TEST_OBJ_DIR), "/bits.log"}, "a");
    $fwrite(fd, "%b\n", {a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15});
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
