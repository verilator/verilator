// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  int arr_default_scalar[4][4];
  int row[4];
  int arr_default_array[2][4];
  int arr_mixed_default[2][3];

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

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
