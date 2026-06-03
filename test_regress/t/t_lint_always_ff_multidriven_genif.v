// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t(input wire clk);

  parameter int max_ports = 4;

  logic [max_ports-1:0][7:0] x;

  localparam logic [max_ports-1:0] use_a = 4'b0101;

  for (genvar port = 0; port < max_ports; port++) begin : g
    if (use_a[port]) begin : g_a
      always_ff @(posedge clk) x[max_ports - port - 1] <= "a";
    end else begin : g_b
      always_ff @(posedge clk) x[max_ports - port - 1] <= "b";
    end
  end

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
