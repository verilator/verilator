// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkf(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%0f exp=%0f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub_a (
    input real i1[1:2]
);
endmodule

module sub_b (
    input real i2[2:1]
);
  sub_a sub_a (.i1(i2));
endmodule

module t;
  real i2[2:1];

  sub_b sub_b (.i2);

  initial begin
    i2[2] = 2.22;
    i2[1] = 1.11;
    #1;
    `checkf(i2[2], 2.22);
    `checkf(i2[1], 1.11);
    `checkf(sub_b.i2[2], 2.22);
    `checkf(sub_b.i2[1], 1.11);
    `checkf(sub_b.sub_a.i1[2], 1.11);
    `checkf(sub_b.sub_a.i1[1], 2.22);
  end

endmodule
