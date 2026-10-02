// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Unpacked array parameter values with equal elements at different indices are different
// values, so the instances given them must not share a module specialization.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef int arr_t[4];

// Sets one element only, so the constant value has that element and a default for the others
function automatic arr_t one_hot(int idx);
  one_hot[idx] = 5;
endfunction

module sub #(
    parameter arr_t ARR = '{default: 0}
) (
    output arr_t o
);
  assign o = ARR;
endmodule

module t;
  arr_t o1;
  arr_t o2;

  sub #(.ARR(one_hot(1))) u1 (.o(o1));
  sub #(.ARR(one_hot(2))) u2 (.o(o2));

  // Without $finish, which could come before the outputs: the simulation ends, and runs the final
  // blocks, once time zero has run
  final begin
    `checkd(o1[1], 5);
    `checkd(o1[2], 0);
    `checkd(o2[1], 0);
    `checkd(o2[2], 5);
    $write("*-* All Finished *-*\n");
  end
endmodule
