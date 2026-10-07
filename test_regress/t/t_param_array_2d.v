// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jonathan Drolet
// SPDX-License-Identifier: CC0-1.0

// Overrides of multidimensional unpacked array parameters, with each instance checking the
// elements, rows, widths and generate choices it was given.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Given an element
module baz #(
    parameter integer hetero_type_p = -1,
    parameter integer EXP = -1
) ();
  initial `checkd(hetero_type_p, EXP);
endmodule

// Selecting elements to pass down (issue #2272), with element (r, c) expected as MUL * r + c,
// or all zeros when MUL is 0
module foo #(
    parameter integer num_tiles_x_p = 4,
    parameter integer num_tiles_y_p = 4,
    // verilog_format: off
    parameter integer hetero_type_vec_p[0:num_tiles_y_p-2][0:num_tiles_x_p-1]
        = '{(num_tiles_y_p - 1){'{num_tiles_x_p{'0}}}},
    // verilog_format: on
    parameter integer MUL = 0
) ();
  genvar r, c;
  for (r = 1; r < num_tiles_y_p; r = r + 1) begin : y
    for (c = 0; c < num_tiles_x_p; c = c + 1) begin : x
      baz #(
          .hetero_type_p(hetero_type_vec_p[r-1][c]),
          .EXP(MUL == 0 ? 0 : MUL * (r - 1) + c)
      ) baz_i ();
    end
  end
endmodule

// Given the whole array, selecting an element in a parameter default (issue #2272)
module idx #(
    parameter int Y = 1,
    parameter int X = 1,
    parameter int idx_y = 1,
    parameter int idx_x = 0,
    parameter int vec_p[Y:1][0:X-1] = '{default: '{default: 0}},
    parameter int hetero_type_p = vec_p[idx_y][idx_x],
    parameter int EXP = 0
) ();
  initial `checkd(hetero_type_p, EXP);
endmodule

// Given a row
module row #(
    parameter logic [6:0] R[3:1] = '{default: '0},
    parameter int EXP_SUM = 0
) ();
  initial `checkd(int'(R[3]) + int'(R[2]) + int'(R[1]), EXP_SUM);
endmodule

// Given an array of arrays, using its elements in widths and generate conditions, and
// passing rows down
module grid #(
    parameter logic [6:0] P[2:1][3:1] = '{default: '{default: 7'd1}},
    parameter int EXP_P13 = 1,
    parameter int EXP_SUM1 = 3,
    parameter int EXP_SUM2 = 3,
    parameter bit EXP_BIG = 1'b0
) ();
  logic [P[1][3]-1:0] d;
  if (P[2][1] > 7'd50) begin : g_big
    initial `checkd(EXP_BIG, 1'b1);
  end
  else begin : g_small
    initial `checkd(EXP_BIG, 1'b0);
  end
  initial `checkd($bits(d), EXP_P13);
  row #(
      .R(P[1]),
      .EXP_SUM(EXP_SUM1)
  ) u_row1 ();
  row #(
      .R(P[2]),
      .EXP_SUM(EXP_SUM2)
  ) u_row2 ();
endmodule

// Given a three-dimensional array
module cube #(
    parameter int C[2][3][2] = '{default: 0},
    parameter int EXP_C120 = 0,
    parameter int EXP_C011 = 0
) ();
  localparam int C120 = C[1][2][0];
  initial `checkd(C120, EXP_C120);
  baz #(
      .hetero_type_p(C[0][1][1]),
      .EXP(EXP_C011)
  ) u_elem ();
endmodule

module t;
  localparam int V[2:1][0:2] = '{'{1, 2, 3}, '{4, 5, 6}};

  // Built by a constant function, element by element and by rows
  typedef int arr_t[3:1][0:1];
  typedef struct {
    int a;
    int b;
  } s_t;
  typedef s_t sarr_t[2][2];
  function automatic arr_t f_arr();
    for (int i = 1; i <= 3; ++i) for (int j = 0; j < 2; ++j) f_arr[i][j] = 10 * i + j;
    f_arr[2] = f_arr[3];
  endfunction
  function automatic sarr_t f_sarr();
    foreach (f_sarr[i, j]) f_sarr[i][j].b = 10 * i + j;
    f_sarr[1][0].a = 7;
  endfunction
  function automatic int f_sum(arr_t a);
    f_sum = 0;
    foreach (a[i, j]) f_sum += a[i][j];
  endfunction
  // Comparisons, and writes out of bounds, which are ignored (IEEE 1800-2023 7.4.6)
  function automatic int f_compare();
    arr_t a;
    arr_t b;
    arr_t exp_b;
    a = f_arr();
    b = a;
    for (int i = 0; i < 3; ++i) b[i][1] = 5;
    exp_b = '{'{30, 31}, '{30, 5}, '{10, 5}};
    f_compare = int'({29'(0), b == exp_b, a == f_arr(), a != b});
  endfunction
  localparam arr_t ARR = f_arr();
  localparam sarr_t SARR = f_sarr();
  localparam int SUM = f_sum(ARR);
  localparam int COMPARE = f_compare();

  foo u_foo_default ();
  foo #(
      .num_tiles_x_p(3),
      .num_tiles_y_p(3),
      .hetero_type_vec_p('{'{0, 1, 2}, '{10, 11, 12}}),
      .MUL(10)
  ) u_foo ();

  for (genvar r = 1; r <= 2; ++r) begin : g_y
    for (genvar c = 0; c < 3; ++c) begin : g_x
      idx #(
          .Y(2),
          .X(3),
          .idx_y(r),
          .idx_x(c),
          .vec_p(V),
          .EXP(r == 2 ? c + 1 : c + 4)
      ) u_idx ();
    end
  end

  grid u_grid_default ();
  grid #(
      .P('{'{7'd3, 7'd2, 7'd60}, '{7'd11, 7'd12, 7'd13}}),
      .EXP_P13(11),
      .EXP_SUM1(36),
      .EXP_SUM2(65),
      .EXP_BIG(1'b1)
  ) u_grid ();

  cube #(
      .C('{'{'{0, 1}, '{2, 3}, '{4, 5}}, '{'{6, 7}, '{8, 9}, '{10, 11}}}),
      .EXP_C120(10),
      .EXP_C011(3)
  ) u_cube ();

  initial begin
    `checkd(ARR[1][0], 10);
    `checkd(ARR[1][1], 11);
    `checkd(ARR[2][0], 30);
    `checkd(ARR[2][1], 31);
    `checkd(ARR[3][1], 31);
    `checkd(SARR[0][1].b, 1);
    `checkd(SARR[1][0].a, 7);
    `checkd(SARR[1][1].a, 0);
    `checkd(SARR[1][1].b, 11);
    `checkd(SUM, 143);
    `checkd(COMPARE, 7);
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
