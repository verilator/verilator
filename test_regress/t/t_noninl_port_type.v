// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module top;

  int x, y, z;
  int out [3];

  sub sub_i(x, y, z, out);

  initial begin
    x = 2;
    y = 1;
    z = 3;
    #1;
    `checkh(out[0], 1);
    `checkh(out[1], 2);
    `checkh(out[2], 3);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule

module sub(
  input int a,
  input int b,
  input int c,
  output int sorted [3]
);

  /* verilator no_inline_module */

  always_comb begin
    sorted = '{a, b, c};
    sorted.sort;
  end

endmodule
