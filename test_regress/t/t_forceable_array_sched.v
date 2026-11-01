// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(g,e) do if ((g) !== (e)) begin $write("%%Error: %s:%0d: got=%x exp=%x\n", `__FILE__,`__LINE__, (g),(e)); `stop; end while(0)
// verilog_format: on

module t;
  bit clk;
  bit data;
  bit a[1]  /* verilator forceable */;
  bit b[1];
  typedef logic [64:0] row_t[3:1];
  typedef row_t matrix_t[-1:0];
  matrix_t source_array;
  matrix_t nba_array  /* verilator forceable */;
  matrix_t blocking_array  /* verilator forceable */;
  matrix_t nba_copy;
  matrix_t blocking_copy;
  logic [64:0] force_data;

  assign b = a;
  assign nba_copy = nba_array;
  assign blocking_copy = blocking_array;

  always @(posedge clk) begin
    a[0] <= data;
    foreach (source_array[i, j]) begin
      nba_array[i][j] <= source_array[i][j];
      blocking_array[i][j] = source_array[i][j];
    end
  end

  initial begin
    for (int cycle = 0; cycle < 6; ++cycle) begin
      data = ~cycle[0];
      foreach (source_array[i, j]) begin
        source_array[i][j] = 65'h1_1234_5678_9abc_def0 ^ 65'(cycle * 13 + i * 3 + j);
      end
      force_data = 65'h1_fedc_ba98_7654_3210 ^ 65'(cycle);
      if (cycle == 2) begin
        force nba_array[-1][2] = force_data;
        force blocking_array[0][1] = force_data;
      end
      if (cycle == 4) begin
        release nba_array[-1][2];
        release blocking_array[0][1];
      end
      #1 clk = 1;
      #1;
      `checkh(b[0], data);
      foreach (nba_copy[i, j]) begin
        `checkh(nba_copy[i][j],
                (cycle >= 2 && cycle < 4 && i == -1 && j == 2) ? force_data : source_array[i][j]);
        `checkh(blocking_copy[i][j],
                (cycle >= 2 && cycle < 4 && i == 0 && j == 1) ? force_data : source_array[i][j]);
      end
      clk = 0;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
