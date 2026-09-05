// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  typedef struct {
    int         i;
    logic [7:0] b;
  } unpacked_t;

  typedef struct {
    int         x;
    logic [3:0] y;
  } inner_t;

  typedef struct {
    inner_t in;
    int     sub[2];
  } nested_t;

  typedef struct packed {
    int         i;
    logic [7:0] b;
  } packed_t;

  int arr_default_scalar[4][4];
  int row[4];
  int arr_default_array[2][4];
  int arr_mixed_default[2][3];
  unpacked_t arr_default_ustruct[3];
  unpacked_t arr_default_ustruct_2d[2][3];
  unpacked_t ustruct;
  unpacked_t arr_default_ustruct_var[3];
  packed_t arr_default_pstruct[3];
  nested_t arr_nested[2];
  nested_t nested_scalar;
  unpacked_t arr_nested_default[3];

  initial begin
    arr_default_scalar = '{default: 0};
    foreach (arr_default_scalar[i, j]) begin
      if (arr_default_scalar[i][j] != 0) $stop;
    end

    row = '{1, 2, 3, 4};
    arr_default_array = '{default: row};
    foreach (arr_default_array[i, j]) begin
      if (arr_default_array[i][j] != row[j]) $stop;
    end

    arr_mixed_default = '{0: '{0: 1, default: 3}, default: '{default: 2}};
    if (arr_mixed_default[0][0] != 1) $stop;
    if (arr_mixed_default[0][1] != 3) $stop;
    if (arr_mixed_default[0][2] != 3) $stop;
    if (arr_mixed_default[1][0] != 2) $stop;
    if (arr_mixed_default[1][1] != 2) $stop;
    if (arr_mixed_default[1][2] != 2) $stop;

    arr_default_ustruct = '{default: '0};
    foreach (arr_default_ustruct[i]) begin
      if (arr_default_ustruct[i].i != 0) $stop;
      if (arr_default_ustruct[i].b != 0) $stop;
    end

    arr_default_ustruct_2d = '{default: '1};
    foreach (arr_default_ustruct_2d[i, j]) begin
      if (arr_default_ustruct_2d[i][j].i != -1) $stop;
      if (arr_default_ustruct_2d[i][j].b != 8'hff) $stop;
    end

    ustruct = '{i: 1, b: 8'h23};
    arr_default_ustruct_var = '{default: ustruct};
    foreach (arr_default_ustruct_var[i]) begin
      if (arr_default_ustruct_var[i].i != 1) $stop;
      if (arr_default_ustruct_var[i].b != 8'h23) $stop;
    end

    arr_default_pstruct = '{default: '0};
    foreach (arr_default_pstruct[i]) begin
      if (arr_default_pstruct[i].i != 0) $stop;
      if (arr_default_pstruct[i].b != 0) $stop;
    end

    // Nested unpacked aggregates must fill member-wise, not take the value whole
    nested_scalar = '{default: '1};
    if (nested_scalar.in.x != -1) $stop;
    if (nested_scalar.in.y != 4'hf) $stop;
    if (nested_scalar.sub[0] != -1) $stop;
    if (nested_scalar.sub[1] != -1) $stop;

    arr_nested = '{default: '1};
    foreach (arr_nested[i]) begin
      if (arr_nested[i].in.x != -1) $stop;
      if (arr_nested[i].in.y != 4'hf) $stop;
      if (arr_nested[i].sub[0] != -1) $stop;
      if (arr_nested[i].sub[1] != -1) $stop;
    end

    arr_nested_default = '{default: '{default: '1}};
    foreach (arr_nested_default[i]) begin
      if (arr_nested_default[i].i != -1) $stop;
      if (arr_nested_default[i].b != 8'hff) $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
