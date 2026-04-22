// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// 3D interface instance arrays.  Ensures arbitrary rank, not just 2D.

interface simple_if;
  logic [15:0] data;
endinterface

module t;
  localparam int A = 2;
  localparam int B = 2;
  localparam int C = 3;

  simple_if bus [A-1:0][B-1:0][C-1:0] ();

  genvar gi, gj, gk;
  generate
    for (gi = 0; gi < A; gi++) begin : g_a
      for (gj = 0; gj < B; gj++) begin : g_b
        for (gk = 0; gk < C; gk++) begin : g_c
          initial bus[gi][gj][gk].data = 16'(gi * B * C + gj * C + gk + 1);
        end
      end
    end
  endgenerate

  logic [15:0] chk [A-1:0][B-1:0][C-1:0];
  generate
    for (gi = 0; gi < A; gi++) begin : g_a_chk
      for (gj = 0; gj < B; gj++) begin : g_b_chk
        for (gk = 0; gk < C; gk++) begin : g_c_chk
          always_comb chk[gi][gj][gk] = bus[gi][gj][gk].data;
        end
      end
    end
  endgenerate

  initial begin
    #1;
    for (int i = 0; i < A; i++) begin
      for (int j = 0; j < B; j++) begin
        for (int k = 0; k < C; k++) begin
          if (chk[i][j][k] !== 16'(i * B * C + j * C + k + 1)) begin
            $write("%%Error: bus[%0d][%0d][%0d].data=%0d expected %0d\n",
                   i, j, k, chk[i][j][k], i * B * C + j * C + k + 1);
            $stop;
          end
        end
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
