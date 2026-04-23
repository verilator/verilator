// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// outer_if contains inner_if; an array of outer_if is passed as a port to
// a submodule which reaches through to inner_if's signal.  Exercises
// hierarchical iface reference across the fanned-out multi-dim port.

interface inner_if;
  logic [7:0] data;
endinterface

interface outer_if;
  inner_if inner ();
  logic [7:0] tag;
endinterface

module sink (
    outer_if b[1:0][1:0]
);
  logic [7:0] chk_tag[1:0][1:0];
  logic [7:0] chk_inner[1:0][1:0];
  genvar gi, gj;
  generate
    for (gi = 0; gi < 2; gi++) begin : g_a
      for (gj = 0; gj < 2; gj++) begin : g_b
        always_comb chk_tag[gi][gj] = b[gi][gj].tag;
        always_comb chk_inner[gi][gj] = b[gi][gj].inner.data;
      end
    end
  endgenerate
endmodule

module t;
  outer_if oarr[1:0][1:0] ();
  sink inst (.b(oarr));

  genvar gi, gj;
  generate
    for (gi = 0; gi < 2; gi++) begin : g_drive_a
      for (gj = 0; gj < 2; gj++) begin : g_drive_b
        initial begin
          oarr[gi][gj].tag = 8'(gi * 16 + gj);
          oarr[gi][gj].inner.data = 8'(gi * 2 + gj + 100);
        end
      end
    end
  endgenerate

  initial begin
    #1;
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j < 2; j++) begin
        if (inst.chk_tag[i][j] !== 8'(i * 16 + j)) begin
          $write("%%Error: chk_tag[%0d][%0d]=%0d expected %0d\n",
                 i, j, inst.chk_tag[i][j], i * 16 + j);
          $stop;
        end
        if (inst.chk_inner[i][j] !== 8'(i * 2 + j + 100)) begin
          $write("%%Error: chk_inner[%0d][%0d]=%0d expected %0d\n",
                 i, j, inst.chk_inner[i][j], i * 2 + j + 100);
          $stop;
        end
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
