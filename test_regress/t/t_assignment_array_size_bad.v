// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

typedef int arr4_t[4];
typedef int arr3_t[3];
typedef int arr2x4_t[2][4];
typedef int arr2x3_t[2][3];

module sub #(
    parameter arr3_t P = '{default: 0},
    parameter arr2x3_t P2 = '{default: 0}
);
endmodule

module t;
  localparam arr4_t ARR4 = '{1, 2, 3, 4};
  localparam arr2x4_t ARR2X4 = '{'{1, 2, 3, 4}, '{5, 6, 7, 8}};

  localparam arr3_t PARAM3 = ARR4;
  localparam arr2x3_t PARAM2X3 = ARR2X4;
  function automatic arr4_t f_return();
    return ARR4;
  endfunction
  localparam arr3_t RETURN3 = f_return();
  function automatic int f_arg(arr3_t a);
    return a[0];
  endfunction
  localparam int ARG3 = f_arg(ARR4);
  sub #(.P(ARR4)) i_sub ();
  sub #(.P2(ARR2X4)) i_sub2 ();
endmodule
