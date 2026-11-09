// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  int value0, width0, value1, width1;
  // Overrides without a value keep the defaults
  sub #(.P(), .T()) s0 (.value(value0), .width(width0));
  sub #(.P(2), .T()) s1 (.value(value1), .width(width1));

  // Without $finish, which could come before the outputs of the hierarchical blocks: the
  // simulation ends, and runs the final blocks, once time zero has run
  final begin
    `checkd(value0, 1);
    `checkd(width0, 32);
    `checkd(value1, 2);
    `checkd(width1, 32);
    $write("*-* All Finished *-*\n");
  end
endmodule

module sub #(
    parameter int P = 1,
    parameter type T = int
) (
    output int value,
    output int width
);
  /*verilator hier_block*/
  assign value = P;
  assign width = $bits(T);
endmodule
