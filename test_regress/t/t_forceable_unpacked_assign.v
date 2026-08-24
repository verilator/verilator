// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Nikolai Kumar
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(g,e) do if ((g) !== (e)) begin $write("%%Error: %s:%0d: got=%x exp=%x\n", `__FILE__,`__LINE__, (g),(e)); `stop; end while(0)
`define checks(g,e) do if ((g) != (e)) begin $write("%%Error: %s:%0d: got='%s' exp='%s'\n", `__FILE__,`__LINE__, (g),(e)); `stop; end while(0)
// verilog_format: on

module t;
  logic var_en[0:1]  /*verilator forceable*/;
  logic copy_en[0:1];
  logic sig;
  typedef logic [6:0] row_t[3:1];
  typedef row_t matrix_t[-1:0];
  typedef logic [64:0] wide_array_t[2:4];
  matrix_t matrix  /*verilator forceable*/;
  matrix_t matrix_copy;
  matrix_t matrix_expected;
  wide_array_t wide_array  /*verilator forceable*/;
  wide_array_t wide_copy;
  wide_array_t wide_expected;

  task check_arrays;
    matrix_copy = matrix;
    wide_copy = wide_array;
    foreach (matrix_copy[i, j]) `checkh(matrix_copy[i][j], matrix_expected[i][j]);
    foreach (wide_copy[i]) `checkh(wide_copy[i], wide_expected[i]);
    `checks($sformatf("%p", matrix), $sformatf("%p", matrix_expected));
    `checks($sformatf("%p", wide_array), $sformatf("%p", wide_expected));
  endtask

  initial begin
    var_en[0] = 1'b0;
    var_en[1] = 1'b0;
  end

  //verilator lint_off IEEEMAYDEPRECATE
  initial assign sig = ($sformatf("%p", var_en) != "");
  //verilator lint_on IEEEMAYDEPRECATE

  initial begin
    #1;
    force var_en[0] = 1'b1;
    #1;
    `checkh(var_en[0], 1'b1);
    `checkh(var_en[1], 1'b0);
    `checkh(sig, 1'b1);
    copy_en = var_en;
    `checkh(copy_en[0], 1'b1);
    `checkh(copy_en[1], 1'b0);
    `checks($sformatf("%p", var_en), $sformatf("%p", copy_en));

    for (int cycle = 0; cycle < 3; ++cycle) begin
      foreach (matrix[i, j]) begin
        matrix[i][j] = 7'(cycle * 13 + i * 3 + j);
        matrix_expected[i][j] = 7'(cycle * 13 + i * 3 + j);
      end
      foreach (wide_array[i]) begin
        wide_array[i] = 65'h1_1234_5678_9abc_def0 ^ 65'(cycle * 7 + i);
        wide_expected[i] = 65'h1_1234_5678_9abc_def0 ^ 65'(cycle * 7 + i);
      end
      #1;
      check_arrays();

      force matrix[-1][2] = 7'h65;
      force wide_array[3][35:29] = 7'h5a;
      matrix_expected[-1][2] = 7'h65;
      wide_expected[3][35:29] = 7'h5a;
      check_arrays();

      release matrix[-1][2];
      release wide_array[3];
      check_arrays();

      matrix[0][1] = 7'(cycle + 40);
      wide_array[4] = 65'(cycle + 50);
      matrix_expected[0][1] = 7'(cycle + 40);
      wide_expected[4] = 65'(cycle + 50);
      #1;
      check_arrays();
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
