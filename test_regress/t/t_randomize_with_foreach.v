// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Grid2D;
  rand bit [4:0] grid[3][3];
endclass

class Grid3D;
  rand bit [3:0] cube[2][2][2];
endclass

module t;
  initial begin
    automatic Grid2D g2 = new;
    automatic Grid3D g3 = new;
    int res;
    int limit = 6;
    bit [3:0] sarr[2][2];

    // 2-D array multi-index foreach
    res = g2.randomize() with {
      foreach (grid[i, j]) grid[i][j] inside {[1:9]};
    };
    `checkd(res, 1);
    for (int i = 0; i < 3; i++) begin
      for (int j = 0; j < 3; j++) begin
        `checkd(g2.grid[i][j] >= 5'd1 && g2.grid[i][j] <= 5'd9, 1);
      end
    end

    // 2-D array with argument and external variable capture
    res = g2.randomize(grid) with {
      foreach (grid[i, j]) grid[i][j] < limit;
      foreach (grid[i, j]) grid[i][j] > 0;
    };
    `checkd(res, 1);
    for (int i = 0; i < 3; i++) begin
      for (int j = 0; j < 3; j++) begin
        `checkd(g2.grid[i][j] > 5'd0 && g2.grid[i][j] < 5'd6, 1);
      end
    end

    // 3-D array multi-index foreach
    res = g3.randomize() with {
      foreach (cube[i, j, k]) cube[i][j][k] inside {[2:7]};
    };
    `checkd(res, 1);
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j < 2; j++) begin
        for (int k = 0; k < 2; k++) begin
          `checkd(g3.cube[i][j][k] >= 4'd2 && g3.cube[i][j][k] <= 4'd7, 1);
        end
      end
    end

    // std::randomize with multi-index foreach
    res = std::randomize(sarr) with {
      foreach (sarr[i, j]) sarr[i][j] inside {[3:5]};
    };
    `checkd(res, 1);
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j < 2; j++) begin
        `checkd(sarr[i][j] >= 4'd3 && sarr[i][j] <= 4'd5, 1);
      end
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
