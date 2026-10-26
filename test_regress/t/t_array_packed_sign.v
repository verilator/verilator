// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Test to check whether the following spec is properly implemented.
// In IEEE 1800-2023 7.4.1 Packed arrays:
//   If a packed array is declared as signed, then the array viewed as a single
//   vector shall be signed. The individual elements of the array are unsigned
//   unless they are of a named type declared as signed.

module t;
  typedef logic signed [2:0] named_t;
  typedef named_t [1:0] named_named_t;
  typedef logic signed [1:0][2:0] named_unnamed_t;

  named_named_t [1:0] named_named;
  named_t [1:0][1:0] named_2d;
  named_unnamed_t [1:0] named_unnamed;
  logic signed [1:0][1:0][2:0] unnamed;

  initial begin
    logic signed [11:0] whole_result;
    logic signed [5:0] slice_result;
    logic signed [2:0] element_result;

    // Set 1 to MSB(=sign bit)
    named_named = 12'b100000_000000;
    named_2d = 12'b100000_000000;
    named_unnamed = 12'b100000_000000;
    unnamed = 12'b100000_000000;

    whole_result = $signed((named_named >>> 1) >> 11);
    `checkd(whole_result, 0);
    slice_result = $signed((named_named[1] >>> 1) >> 5);
    `checkd(slice_result, 0);
    element_result = $signed((named_named[1][1] >>> 1) >> 2);
    `checkd(element_result, 1);

    whole_result = $signed((named_2d >>> 1) >> 11);
    `checkd(whole_result, 0);
    element_result = $signed((named_2d[1][1] >>> 1) >> 2);
    `checkd(element_result, 1);

    whole_result = $signed((named_unnamed >>> 1) >> 11);
    `checkd(whole_result, 0);
    slice_result = $signed((named_unnamed[1] >>> 1) >> 5);
    `checkd(slice_result, 1);
    element_result = $signed((named_unnamed[1][1] >>> 1) >> 2);
    `checkd(element_result, 0);

    whole_result = $signed((unnamed >>> 1) >> 11);
    `checkd(whole_result, 1);
    slice_result = $signed((unnamed[1] >>> 1) >> 5);
    `checkd(slice_result, 0);
    element_result = $signed((unnamed[1][1] >>> 1) >> 2);
    `checkd(element_result, 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
