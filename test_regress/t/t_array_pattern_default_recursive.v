// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Verilator Authors
// SPDX-License-Identifier: CC0-1.0

module t;

  int arr_default_scalar[4][4];
  int row[4];
  int arr_default_array[2][4];

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

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
