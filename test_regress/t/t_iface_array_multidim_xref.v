// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Cross-hierarchy dotted refs through a multi-dim iface array of a
// parameterized interface.  Exercises IfaceCapture plus the multi-dim
// dotted-access resolver together.

interface bus_if #(parameter int W = 8);
  logic [W-1:0] data;
endinterface

// Wrapper holding the multi-dim iface array; parent reads its cells via dots.
module holder;
  localparam int A = 2;
  localparam int B = 3;

  bus_if #(.W(8)) bus [A-1:0][B-1:0] ();

  genvar gi, gj;
  generate
    for (gi = 0; gi < A; gi++) begin : g_a
      for (gj = 0; gj < B; gj++) begin : g_b
        initial bus[gi][gj].data = 8'(gi * B + gj + 5);
      end
    end
  endgenerate
endmodule

module t;
  holder h();

  initial begin
    #1;
    if (h.bus[0][0].data !== 8'd5) begin
      $write("%%Error: h.bus[0][0].data=%0d expected 5\n", h.bus[0][0].data);
      $stop;
    end
    if (h.bus[0][1].data !== 8'd6) begin
      $write("%%Error: h.bus[0][1].data=%0d expected 6\n", h.bus[0][1].data);
      $stop;
    end
    if (h.bus[0][2].data !== 8'd7) begin
      $write("%%Error: h.bus[0][2].data=%0d expected 7\n", h.bus[0][2].data);
      $stop;
    end
    if (h.bus[1][0].data !== 8'd8) begin
      $write("%%Error: h.bus[1][0].data=%0d expected 8\n", h.bus[1][0].data);
      $stop;
    end
    if (h.bus[1][1].data !== 8'd9) begin
      $write("%%Error: h.bus[1][1].data=%0d expected 9\n", h.bus[1][1].data);
      $stop;
    end
    if (h.bus[1][2].data !== 8'd10) begin
      $write("%%Error: h.bus[1][2].data=%0d expected 10\n", h.bus[1][2].data);
      $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
