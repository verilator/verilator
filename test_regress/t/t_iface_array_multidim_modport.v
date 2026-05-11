// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Multi-dim iface array ports typed with a modport (both source and sink).
// Mirrors 1D modport-port coverage in t_interface_array_loop for the
// multi-dim pin-fanout path.

interface simple_if;
  logic [7:0] data;
  modport source(output data);
  modport sink(input data);
endinterface

module src (
    simple_if.source b[1:0][2:0]
);
  genvar gi, gj;
  generate
    for (gi = 0; gi < 2; gi++) begin : g_a
      for (gj = 0; gj < 3; gj++) begin : g_b
        initial b[gi][gj].data = 8'(gi * 3 + gj + 20);
      end
    end
  endgenerate
endmodule

module snk (
    simple_if.sink b[1:0][2:0]
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
  src src_inst (.b(bus));
  snk snk_inst (.b(bus));

  initial begin
    #1;
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j < 3; j++) begin
        if (snk_inst.chk[i][j] !== 8'(i * 3 + j + 20)) begin
          $write("%%Error: chk[%0d][%0d]=%0d expected %0d\n",
                 i, j, snk_inst.chk[i][j], i * 3 + j + 20);
          $stop;
        end
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
