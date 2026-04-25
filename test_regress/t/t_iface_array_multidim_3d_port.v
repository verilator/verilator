// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// 3D iface-array port passed to a submodule.  t_iface_array_multidim_3d
// covers 3D local declaration; this covers 3D through a port.

interface simple_if;
  logic [15:0] data;
endinterface

module sink (
    simple_if b[1:0][1:0][2:0]
);
  logic [15:0] chk[1:0][1:0][2:0];
  genvar gi, gj, gk;
  generate
    for (gi = 0; gi < 2; gi++) begin : g_a
      for (gj = 0; gj < 2; gj++) begin : g_b
        for (gk = 0; gk < 3; gk++) begin : g_c
          always_comb chk[gi][gj][gk] = b[gi][gj][gk].data;
        end
      end
    end
  endgenerate
endmodule

module t;
  simple_if bus[1:0][1:0][2:0] ();
  sink inst (.b(bus));

  genvar gi, gj, gk;
  generate
    for (gi = 0; gi < 2; gi++) begin : g_drive_a
      for (gj = 0; gj < 2; gj++) begin : g_drive_b
        for (gk = 0; gk < 3; gk++) begin : g_drive_c
          initial bus[gi][gj][gk].data = 16'(gi * 6 + gj * 3 + gk + 1);
        end
      end
    end
  endgenerate

  initial begin
    #1;
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j < 2; j++) begin
        for (int k = 0; k < 3; k++) begin
          if (inst.chk[i][j][k] !== 16'(i * 6 + j * 3 + k + 1)) begin
            $write("%%Error: chk[%0d][%0d][%0d]=%0d expected %0d\n",
                   i, j, k, inst.chk[i][j][k], i * 6 + j * 3 + k + 1);
            $stop;
          end
        end
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
