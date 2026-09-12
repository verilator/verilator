// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(g,e) do if ((g) !== (e)) begin $write("%%Error: %s:%0d: got=%x exp=%x\n", `__FILE__,`__LINE__, (g),(e)); `stop; end while(0)
`define checks(g,e) do if ((g) != (e)) begin $write("%%Error: %s:%0d: got='%s' exp='%s'\n", `__FILE__,`__LINE__, (g),(e)); `stop; end while(0)
// verilog_format: on

module t;
  bit a[1]  /* verilator forceable */;
  bit source_array[1];
  bit result_array[1];
  typedef logic [6:0] row_t[3:1];
  typedef row_t matrix_t[-1:0];
  typedef logic [64:0] wide_array_t[2:4];
  matrix_t matrix  /* verilator forceable */;
  matrix_t matrix_source;
  matrix_t matrix_result;
  wide_array_t wide_array  /* verilator forceable */;
  wide_array_t wide_source;
  wide_array_t wide_result;

  initial begin
    for (int cycle = 0; cycle < 6; ++cycle) begin
      #1;
      source_array[0] = ~cycle[0];
      a = source_array;
      result_array = a;
      `checkh(result_array[0], source_array[0]);

      foreach (matrix_source[i, j]) matrix_source[i][j] = 7'(cycle * 13 + i * 3 + j);
      foreach (wide_source[i]) wide_source[i] = 65'h1_1234_5678_9abc_def0 ^ 65'(cycle * 7 + i);
      matrix = matrix_source;
      wide_array = wide_source;
      matrix_result = matrix;
      wide_result = wide_array;
      foreach (matrix_result[i, j]) `checkh(matrix_result[i][j], matrix_source[i][j]);
      foreach (wide_result[i]) `checkh(wide_result[i], wide_source[i]);

      force matrix[-1][2] = 7'h65;
      force wide_array[3] = 65'h1_5678_9abc_def0_1234;
      matrix = matrix_source;
      wide_array = wide_source;
      matrix_result = matrix;
      wide_result = wide_array;
      foreach (matrix_result[i, j]) begin
        `checkh(matrix_result[i][j], (i == -1 && j == 2) ? 7'h65 : matrix_source[i][j]);
      end
      foreach (wide_result[i]) begin
        `checkh(wide_result[i], i == 3 ? 65'h1_5678_9abc_def0_1234 : wide_source[i]);
      end
      `checks($sformatf("%p", matrix), $sformatf("%p", matrix_result));
      `checks($sformatf("%p", wide_array), $sformatf("%p", wide_result));

      release matrix[-1][2];
      release wide_array[3];
      matrix = matrix_source;
      wide_array = wide_source;
      matrix_result = matrix;
      wide_result = wide_array;
      foreach (matrix_result[i, j]) `checkh(matrix_result[i][j], matrix_source[i][j]);
      foreach (wide_result[i]) `checkh(wide_result[i], wide_source[i]);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
