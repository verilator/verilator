// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Multi-dim iface array port, sink WRITES into the iface signals, top reads.
// Complements t_iface_array_multidim_port (which has sink reading).

interface simple_if;
  logic [7:0] data;
endinterface

module src (simple_if b [1:0][2:0]);
  genvar gi, gj;
  generate
    for (gi = 0; gi < 2; gi++) begin : g_a
      for (gj = 0; gj < 3; gj++) begin : g_b
        initial b[gi][gj].data = 8'(gi * 3 + gj + 50);
      end
    end
  endgenerate
endmodule

module t;
  simple_if bus [1:0][2:0] ();
  src inst (.b(bus));

  initial begin
    #1;
    if (bus[0][0].data !== 8'd50) begin $write("%%Error: bus[0][0]=%0d\n", bus[0][0].data); $stop; end
    if (bus[0][1].data !== 8'd51) begin $write("%%Error: bus[0][1]=%0d\n", bus[0][1].data); $stop; end
    if (bus[0][2].data !== 8'd52) begin $write("%%Error: bus[0][2]=%0d\n", bus[0][2].data); $stop; end
    if (bus[1][0].data !== 8'd53) begin $write("%%Error: bus[1][0]=%0d\n", bus[1][0].data); $stop; end
    if (bus[1][1].data !== 8'd54) begin $write("%%Error: bus[1][1]=%0d\n", bus[1][1].data); $stop; end
    if (bus[1][2].data !== 8'd55) begin $write("%%Error: bus[1][2]=%0d\n", bus[1][2].data); $stop; end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
