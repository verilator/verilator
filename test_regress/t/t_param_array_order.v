// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jonathan Drolet
// SPDX-License-Identifier: CC0-1.0

// Constant arrays given to arrays of the other direction, assigned by the left-to-right order
// of their elements (IEEE 1800-2023 7.6)

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef int be_t[0:3];
typedef int le_t[3:0];

module sub #(
    parameter le_t LE = '{default: 0}
);
  initial begin
    `checkd(LE[3], 10);
    `checkd(LE[0], 13);
  end
endmodule

module t;
  // Issue #6539
  typedef logic [31:0] be_unpacked_arr_t[8];
  typedef logic [31:0] le_unpacked_arr_t[7:0];
  function automatic be_unpacked_arr_t foo();
    be_unpacked_arr_t arr;
    for (int i = 0; i < 8; i++) begin
      arr[i] = i;
    end
    return arr;
  endfunction
  localparam le_unpacked_arr_t LE_PARAM = foo();

  localparam be_t BE = '{10, 11, 12, 13};
  // A parameter, and a pattern returned by a function
  localparam le_t COPY = BE;
  function automatic be_t f_pattern();
    return '{20, 21, 22, 23};
  endfunction
  localparam le_t PATTERN = f_pattern();
  // In a constant function: a copy, a return and an argument
  function automatic int f_copy();
    le_t x;
    x = BE;
    return x[3];
  endfunction
  function automatic le_t f_return();
    return BE;
  endfunction
  function automatic int f_arg(le_t a);
    return a[3];
  endfunction
  localparam int FCOPY = f_copy();
  localparam le_t FRETURN = f_return();
  localparam int FARG = f_arg(BE);
  // Arrays of arrays, and a default
  typedef int be3_t[0:2];
  typedef int be2_t[0:1][0:2];
  typedef int le2_t[1:0][2:0];
  localparam be2_t BE2 = '{'{1, 2, 3}, '{4, 5, 6}};
  localparam le2_t LE2 = BE2;
  localparam be2_t BE2_DEFAULT = '{default: be3_t'{1, 2, 3}};
  localparam le2_t LE2_DEFAULT = BE2_DEFAULT;
  function automatic le2_t f_row();
    f_row[1] = BE2[0];
    f_row[0] = '{7, 8, 9};
  endfunction
  localparam le2_t ROW = f_row();
  function automatic le2_t f_default();
    be2_t x;
    x[0][1] = 5;
    return x;
  endfunction
  localparam le2_t FDEFAULT = f_default();
  // Only the outer, or only the inner level of the other direction
  typedef int outer_t[1:0][0:2];
  typedef int inner_t[0:1][2:0];
  localparam outer_t OUTER = BE2;
  localparam inner_t INNER = BE2;
  // An array of structures containing an array
  typedef struct {
    int a[0:1];
    int b;
  } s_t;
  localparam s_t BES[0:1] = '{'{a: '{1, 2}, b: 3}, '{a: '{4, 5}, b: 6}};
  localparam s_t LES[1:0] = BES;
  localparam be_t BE_DEFAULT = '{1: 7, default: 9};
  localparam le_t LE_DEFAULT = BE_DEFAULT;

  sub #(.LE(BE)) u_sub ();

  initial begin
    for (int i = 0; i < 8; i++) `checkd(LE_PARAM[i], 8 - 1 - i);
    `checkd(COPY[3], 10);
    `checkd(COPY[0], 13);
    `checkd(PATTERN[3], 20);
    `checkd(FCOPY, 10);
    `checkd(FRETURN[3], 10);
    `checkd(FARG, 10);
    `checkd(LE2[1][2], 1);
    `checkd(LE2[1][0], 3);
    `checkd(LE2[0][0], 6);
    `checkd(LE2_DEFAULT[0][2], 1);
    `checkd(LE2_DEFAULT[1][0], 3);
    `checkd(ROW[1][2], 1);
    `checkd(ROW[0][2], 7);
    `checkd(FDEFAULT[1][1], 5);
    `checkd(FDEFAULT[1][2], 0);
    `checkd(OUTER[1][0], 1);
    `checkd(OUTER[0][2], 6);
    `checkd(INNER[0][2], 1);
    `checkd(INNER[1][0], 6);
    `checkd(LES[1].a[0], 1);
    `checkd(LES[1].b, 3);
    `checkd(LES[0].a[1], 5);
    `checkd(LE_DEFAULT[2], 7);
    `checkd(LE_DEFAULT[1], 9);
    // Reversed pattern elements and members
    begin
      typedef struct {int a[3:0];} sle_t;
      localparam le2_t PATTERN2 = '{be3_t'{1, 2, 3}, be3_t'{4, 5, 6}};
      localparam sle_t SMEMBER = '{a: BE};
      localparam be_t BE_B = '{50, 51, 52, 53};
      localparam le_t KEYED[2] = '{1: BE, 0: BE_B};
      `checkd(PATTERN2[1][2], 1);
      `checkd(PATTERN2[1][0], 3);
      `checkd(PATTERN2[0][0], 6);
      `checkd(SMEMBER.a[3], 10);
      `checkd(SMEMBER.a[0], 13);
      `checkd(KEYED[1][3], 10);
      `checkd(KEYED[0][3], 50);
      `checkd(KEYED[0][0], 53);
    end
    // Comparisons, equal by position, and equal only by offset
    begin
      localparam bit EQ_POS = COPY == BE;
      localparam le_t LE_SAMEOFF = '{13, 12, 11, 10};
      localparam bit EQ_OFF = LE_SAMEOFF == BE;
      `checkd(EQ_POS, 1'b1);
      `checkd(EQ_OFF, 1'b0);
    end
    // A conditional of reversed operands
    begin
      localparam le_t CONDP = 1'b1 ? BE : COPY;
      `checkd(CONDP[3], 10);
      `checkd(CONDP[0], 13);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
