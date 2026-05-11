// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Multi-dim iface array passed as a port to a submodule (the point of
// multi-dim iface arrays).  Exercises the multi-dim pin-fanout branch in
// V3Inst::visit(AstPin) and the multi-dim branch in V3Inst::visit(AstVar)
// on the sink's port var.

interface simple_if;
  logic [7:0] data;
endinterface

module sink (
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

module t;
  simple_if bus[1:0][2:0] ();
  sink inst (.b(bus));

  genvar gi, gj;
  generate
    for (gi = 0; gi < 2; gi++) begin : g_drive_a
      for (gj = 0; gj < 3; gj++) begin : g_drive_b
        initial bus[gi][gj].data = 8'(gi * 3 + gj + 1);
      end
    end
  endgenerate

  initial begin
    #1;
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j < 3; j++) begin
        if (inst.chk[i][j] !== 8'(i * 3 + j + 1)) begin
          $write("%%Error: inst.chk[%0d][%0d]=%0d expected %0d\n",
                 i, j, inst.chk[i][j], i * 3 + j + 1);
          $stop;
        end
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
