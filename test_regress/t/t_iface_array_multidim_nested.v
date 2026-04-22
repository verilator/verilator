// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Multi-dim iface array where outer iface contains an inner iface.
// outer_if oarr[A][B](), outer_if holds a single inner_if instance.
// Access via oarr[i][j].inner.data.

interface inner_if;
  logic [7:0] data;
endinterface

interface outer_if;
  inner_if inner();
  logic [7:0] tag;
endinterface

module t;
  localparam int A = 2;
  localparam int B = 2;

  outer_if oarr [A-1:0][B-1:0] ();

  genvar gi, gj;
  generate
    for (gi = 0; gi < A; gi++) begin : g_a
      for (gj = 0; gj < B; gj++) begin : g_b
        initial begin
          oarr[gi][gj].tag = 8'(gi * 16 + gj);
          oarr[gi][gj].inner.data = 8'(gi * B + gj + 100);
        end
      end
    end
  endgenerate

  logic [7:0] chk_tag [A-1:0][B-1:0];
  logic [7:0] chk_inner [A-1:0][B-1:0];
  generate
    for (gi = 0; gi < A; gi++) begin : g_a_chk
      for (gj = 0; gj < B; gj++) begin : g_b_chk
        always_comb chk_tag[gi][gj] = oarr[gi][gj].tag;
        always_comb chk_inner[gi][gj] = oarr[gi][gj].inner.data;
      end
    end
  endgenerate

  initial begin
    #1;
    for (int i = 0; i < A; i++) begin
      for (int j = 0; j < B; j++) begin
        if (chk_tag[i][j] !== 8'(i * 16 + j)) begin
          $write("%%Error: oarr[%0d][%0d].tag=%0d expected %0d\n",
                 i, j, chk_tag[i][j], i * 16 + j);
          $stop;
        end
        if (chk_inner[i][j] !== 8'(i * B + j + 100)) begin
          $write("%%Error: oarr[%0d][%0d].inner.data=%0d expected %0d\n",
                 i, j, chk_inner[i][j], i * B + j + 100);
          $stop;
        end
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
