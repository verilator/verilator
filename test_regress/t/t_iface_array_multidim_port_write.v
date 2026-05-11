// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Multi-dim iface array port, sink WRITES into the iface signals, top reads.
// Complements t_iface_array_multidim_port (which has sink reading).

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface simple_if;
  logic [7:0] data;
endinterface

module src (
    simple_if b[1:0][2:0]
);
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
  simple_if bus[1:0][2:0] ();
  src inst (.b(bus));

  initial begin
    #1;
    `checkd(bus[0][0].data, 8'd50);
    `checkd(bus[0][1].data, 8'd51);
    `checkd(bus[0][2].data, 8'd52);
    `checkd(bus[1][0].data, 8'd53);
    `checkd(bus[1][1].data, 8'd54);
    `checkd(bus[1][2].data, 8'd55);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
