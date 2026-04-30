// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Three-level hierarchy passing a multi-dim iface array by port at each
// boundary.  Top reads leaf's chk array via dotted cross-hier reference,
// which also exercises the multi-dim dotted-access resolver.

interface simple_if;
  logic [7:0] data;
endinterface

module leaf (
    simple_if b[1:0][2:0]
);
  logic [7:0] chk[1:0][2:0];
  genvar gi, gj;
  generate
    for (gi = 0; gi < 2; gi++) begin : g_a
      for (gj = 0; gj < 3; gj++) begin : g_b
        always_comb chk[gi][gj] = b[gi][gj].data;
      end
    end
  endgenerate
endmodule

module mid (
    simple_if b[1:0][2:0]
);
  leaf leaf_inst (.b(b));
endmodule

module t;
  simple_if bus[1:0][2:0] ();
  mid mid_inst (.b(bus));

  genvar gi, gj;
  generate
    for (gi = 0; gi < 2; gi++) begin : g_drive_a
      for (gj = 0; gj < 3; gj++) begin : g_drive_b
        initial bus[gi][gj].data = 8'(gi * 3 + gj + 7);
      end
    end
  endgenerate

  initial begin
    #1;
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j < 3; j++) begin
        if (mid_inst.leaf_inst.chk[i][j] !== 8'(i * 3 + j + 7)) begin
          $write("%%Error: leaf.chk[%0d][%0d]=%0d expected %0d\n",
                 i, j, mid_inst.leaf_inst.chk[i][j], i * 3 + j + 7);
          $stop;
        end
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
